module

public import Basic.Defs
public import Basic.RhoOne
public import Phylogenetics.NMSC.DisplayedTreeModel
public import Phylogenetics.NMSC.Induced
public import Phylogenetics.NMSC.InducedParams
public import Basic.Testing.Trinomial.Tests
public import TOBQMC.Level1Blobs
public import ECToBlob.Section3

/-!
# ECToBlob Remark 3.3: the assumptions of Theorem 3.1 for common models

"The two assumptions of the theorem are met by common models in phylogenomics. The NMSC model with
independent or correlated inheritance satisfies (3.1) provided the network has no anomalous quartets and
that cut edges (which are necessarily tree edges) have positive lengths [8]. The NMSC with common
inheritance, and the displayed tree model (with no coalescent process) also satisfy (3.1) provided only that
cut edges have positive lengths. All of these models also satisfy assumption 2 of Theorem 3.1."
(the paper's text, lines 401-406.)

`Theorem31Assumptions` packages the two assumptions in the form in which `theorem3_1` uses them.

* `remark3_3_nmsc`: the NMSC, for any `0 ≤ ρ ≤ 1`, under the assumption that the quartet tree of a cut edge
  is strictly the most probable. `nmscCF_lt_iff_one_third_lt`, `nmscCF_le_iff_one_third_le`: on a cut-edge
  split this is `1/3 < p_ab|cd`, while the "no anomalous" of [8] (its Definition 2: an anomaly is
  `p_ab|cd < 1/3`) is only `1/3 ≤ p_ab|cd`, which is not enough: see the note at `remark3_3_nmsc`.
* `remark3_3_common`: the NMSC with common inheritance, `ρ = 1`, with positive lengths on cut edges only.
* `displayedCF`, `displayedTreeDist`, `remark3_3_displayed`: the displayed tree model, with no assumption on lengths.

Condition 2 is `CutExchangeable` in the form that the proof of Theorem 3.1 uses. As printed, it is
`pendantChainInvariant_nmscCF` and `pendantChainInvariant_displayedCF` (`PendantChainInvariant`, which implies
`CutExchangeable` by `pendantChainInvariant_cutExchangeable`), and "`p_xy|zw` is determined by the network on
`x, y, z, w` induced from `N⁺`" is `remark3_3_induced_nmsc` and `remark3_3_induced_displayed`. The proof of the printed
form needs the hypothesis on the attachments only, not the one on the core arcs.

The instances of Theorem 3.1 are `Theorem31Assumptions.treeOfBlobs_subset`, and those of Corollary 3.6 are
`corollary3_6_nmsc`, `corollary3_6_common`, `corollary3_6_displayed`. Also: the displayed tree model is the limit of
common inheritance as all lengths grow (`abs_nmscCF_sub_displayedCF_le`, `tendsto_nmscCF_addLength_displayedCF`).

Remark 3.2 for this model: lines 397-398 hold for the concordance factors of lines 278-284 (`displayedRawCF`,
`quartetScore_displayedRawCF_of_resolution`, `remark3_2_no_impact`), and line 400 for those of the convention of lines
289-293 (`displayedCF`, `quartetScore_displayedCF_of_resolution`, `isBinaryTree_of_displayedCF_maximizer`).

Under that convention the counts on a trivial 4-blob are `(n/3, n/3, n/3)` on every sample, so the star and T1 p-values are
`1`, and the star p-value is not asymptotically uniform (`pValues_of_hasTrivialFourBlob`,
`not_asymptoticallyUniform_starPValue`): Lemma 8.1 does not apply there, in the proof of Theorem 8.2.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- **The assumptions of Theorem 3.1**, in the form in which `theorem3_1` uses them, for weights `p` on the
quartet trees: equation (3.1), where "a cut edge separates `a, b` from `c, d`" is "the tree of blobs displays
`ab|cd`"; and condition 2 as `CutExchangeable`. -/
structure Theorem31Assumptions (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ p s
  cut : ∀ s, Displays (treeOfBlobs N) s → ∀ r ∈ s.alternatives, p r < p s
  exchangeable : CutExchangeable N p

/-- **Theorem 3.1** (`ecto:thm3_1`) for a model satisfying its assumptions. -/
theorem Theorem31Assumptions.treeOfBlobs_subset {N : RootedNetwork V E X} {p : QuartetTree X → ℝ}
    (h : Theorem31Assumptions N p) (hN : N.IsPhylogenetic) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hmax : ∀ T', IsUnrootedTree T' → quartetSupport p T' ≤ quartetSupport p T) :
    treeOfBlobs N ⊆ T :=
  theorem3_1 hN p h.nonneg h.cut h.exchangeable hT hmax

/-! ### Gene tree distributions as images -/

section Push

variable {ι : Type*} [Fintype ι]

/-- The law on unrooted gene trees of the tree `g i`, for an index `i` with law `w`. -/
def imageTreeDist (w : ι → ℝ) (g : ι → Finset (Finset X)) : UnrootedGeneTree X → ℝ :=
  fun T => ∑ i, if g i = T.val then w i else 0

omit [Fintype ι] in
private theorem sum_ite_tree {w : ι → ℝ} {g : ι → Finset (Finset X)}
    (hg : ∀ i, w i ≠ 0 → IsUnrootedTree (g i)) (C : UnrootedGeneTree X → ℝ) (i : ι) :
    ∑ T : UnrootedGeneTree X, (if g i = T.val then w i else 0) * C T =
      if h : w i = 0 then 0 else w i * C ⟨g i, hg i h⟩ := by
  split_ifs with h
  · simp [h]
  · rw [Finset.sum_eq_single (⟨g i, hg i h⟩ : UnrootedGeneTree X)]
    · rw [ite_eq_left rfl]
    · intro T _ hne
      rw [ite_eq_right fun h' => hne (Subtype.ext h'.symm), zero_mul]
    · exact fun h' => absurd (mem_univ _) h'

theorem imageTreeDist_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (g : ι → Finset (Finset X))
    (T : UnrootedGeneTree X) : 0 ≤ imageTreeDist w g T :=
  sum_nonneg fun i _ => by
    split_ifs
    · exact hw i
    · exact le_rfl

theorem sum_imageTreeDist {w : ι → ℝ} {g : ι → Finset (Finset X)} (hg : ∀ i, w i ≠ 0 → IsUnrootedTree (g i)) :
    ∑ T, imageTreeDist w g T = ∑ i, w i := by
  unfold imageTreeDist
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := sum_ite_tree hg (fun _ => 1) i
  simp only [mul_one] at h
  rw [h]
  split_ifs with h0
  · exact h0.symm
  · rfl

/-- The mean of a function of the tree under the image law. -/
theorem sum_imageTreeDist_mul {w : ι → ℝ} {g : ι → Finset (Finset X)}
    (hg : ∀ i, w i ≠ 0 → IsUnrootedTree (g i)) (C : Finset (Finset X) → ℝ) :
    ∑ T : UnrootedGeneTree X, imageTreeDist w g T * C T.val = ∑ i, w i * C (g i) := by
  unfold imageTreeDist
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_ite_tree hg (fun T => C T.val) i]
  split_ifs with h0
  · simp [h0]
  · rfl

theorem expectedCF_imageTreeDist {w : ι → ℝ} {g : ι → Finset (Finset X)}
    (hg : ∀ i, w i ≠ 0 → IsUnrootedTree (g i)) (s : QuartetTree X) :
    expectedCF (imageTreeDist w g) s = ∑ i, w i * geneContribution (g i) s := by
  unfold expectedCF imageTreeDist
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_ite_tree hg (fun T => geneContribution T.val s) i]
  split_ifs with h0
  · simp [h0]
  · rfl

end Push

omit [Fintype X] in
/-- What a tree displaying `s` gives to the concordance factors on the taxa of `s`. -/
theorem geneContribution_of_displays [Fintype X] {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {s : QuartetTree X} (hs : Displays T s) :
    geneContribution T s = 1 ∧ ∀ r ∈ s.alternatives, geneContribution T r = 0 := by
  refine ⟨ite_eq_left hs, fun r hr => ?_⟩
  obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
  unfold geneContribution
  rw [ite_eq_right fun h => hrs (hT.displays_unique h hs hrt), ite_eq_right]
  exact fun h => h s (mem_treesOn.2 hrt.symm) hs

/-- The contributions of a tree to the three quartet trees on a set of four taxa sum to one. -/
theorem sum_geneContribution {T : Finset (Finset X)} (hT : IsUnrootedTree T) {q : Finset X}
    (hq : q.card = 4) : ∑ r ∈ treesOn q, geneContribution T r = 1 := by
  by_cases hex : ∃ r ∈ treesOn q, Displays T r
  · obtain ⟨s, hs, hd⟩ := hex
    have hst := mem_treesOn.1 hs
    obtain ⟨h1, h0⟩ := geneContribution_of_displays hT hd
    rw [Finset.sum_eq_single s, h1]
    · intro r hr hne
      exact h0 r (QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 hr).trans hst.symm, hne⟩)
    · exact fun h => absurd hs h
  · push Not at hex
    have hterm : ∀ r ∈ treesOn q, geneContribution T r = 1 / 3 := by
      intro r hr
      unfold geneContribution
      rw [ite_eq_right (hex r hr), ite_eq_left]
      intro r' hr'
      rw [mem_treesOn.1 hr] at hr'
      exact hex r' hr'
    rw [sum_congr rfl hterm, sum_const, card_treesOn hq]
    norm_num

/-- Replacing a taxon in a quartet tree does not change what a tree with a side grouping the two taxa
contributes. -/
theorem geneContribution_eq_of_replace {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : A ∈ T) {s s' : QuartetTree X} {a a' : X} (haA : a ∈ A) (ha'A : a' ∈ A) (has : a ∈ s.taxa)
    (ha's : a' ∉ s.taxa) (hoth : ∀ x ∈ s.taxa, x ≠ a → x ∉ A)
    (hs' : s'.val = s.val.image (fun B => if a ∈ B then insert a' (B.erase a) else B)) :
    geneContribution T s = geneContribution T s' := by
  have hrel := eq_relabelQuartet_swap_of_image ha's hs'
  have hne : a ≠ a' := fun h => ha's (h ▸ has)
  set π := Equiv.swap a a' with hπ
  have htaxa : s'.taxa = s.taxa.map π.toEmbedding := by
    rw [hrel, NMSC.taxa_relabelQuartet]
  have hswap : Equiv.swap a' a = π := Equiv.swap_comm a' a
  have ha's' : a ∉ s'.taxa := by
    rw [htaxa, mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_left]
    exact ha's
  have hoth' : ∀ x ∈ s'.taxa, x ≠ a' → x ∉ A := by
    intro x hx hxa'
    rw [htaxa, mem_map_equiv, Equiv.symm_swap] at hx
    by_cases hxa : x = a
    · subst hxa
      rw [Equiv.swap_apply_left] at hx
      exact absurd hx ha's
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxa'] at hx
      exact hoth x hx hxa
  -- a replacement of a taxon of the quartet trees on either set of taxa
  have hf : ∀ r : QuartetTree X, r.taxa = s.taxa → Displays T r →
      Displays T (NMSC.relabelQuartet π r) := fun r hr hd =>
    displays_relabelQuartet_swap hT hA haA ha'A (hr ▸ ha's) (hr ▸ hoth) hd
  have hb : ∀ r : QuartetTree X, r.taxa = s'.taxa → Displays T r →
      Displays T (NMSC.relabelQuartet π r) := fun r hr hd => by
    have := displays_relabelQuartet_swap hT hA ha'A haA (hr ▸ ha's') (hr ▸ hoth') hd
    rwa [hswap] at this
  have hinv : ∀ r : QuartetTree X, NMSC.relabelQuartet π (NMSC.relabelQuartet π r) = r := fun r => by
    refine Subtype.ext ?_
    change relabelFamily π (relabelFamily π r.val) = r.val
    ext B
    unfold relabelFamily
    simp only [mem_image, exists_exists_and_eq_and]
    have hmm : ∀ C : Finset X, (C.map π.toEmbedding).map π.toEmbedding = C := fun C => by
      ext z
      simp [mem_map_equiv, hπ, Equiv.symm_swap]
    simp only [hmm]
    simp
  have hss' : NMSC.relabelQuartet π s' = s := by
    rw [hrel, hinv]
  have hD : Displays T s ↔ Displays T s' :=
    ⟨fun h => hrel ▸ hf s rfl h, fun h => hss' ▸ hb s' rfl h⟩
  have hS : (∀ r ∈ treesOn s.taxa, ¬ Displays T r) ↔ ∀ r ∈ treesOn s'.taxa, ¬ Displays T r := by
    constructor
    · intro h r hr hd
      have hrt := mem_treesOn.1 hr
      refine h _ (mem_treesOn.2 ?_) (hb r hrt hd)
      rw [NMSC.taxa_relabelQuartet, hrt, htaxa]
      ext z
      simp [mem_map_equiv, hπ, Equiv.symm_swap]
    · intro h r hr hd
      have hrt := mem_treesOn.1 hr
      refine h _ (mem_treesOn.2 ?_) (hf r hrt hd)
      rw [NMSC.taxa_relabelQuartet, hrt, htaxa]
  unfold geneContribution
  simp only [hD, hS]

/-! ### The NMSC with independent or correlated inheritance -/

section NMSC

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

omit [Fintype V] [Fintype E] in
/-- A cut edge of the network is one of the induced networks: having no anomalous quartets, in the form of
`NoAnomalousQuartets`, implies equation (3.1). -/
theorem isTQuartetNonanomalous_of_inducedCutSplit (hN : N.IsPhylogenetic) {p : QuartetTree X → ℝ}
    (h : ∀ s, InducedCutSplit N s → ∀ r ∈ s.alternatives, p r < p s) :
    TOBQMC.IsTQuartetNonanomalous N p := fun s hs =>
  h s (inducedCutSplit_of_displays_treeOfBlobs hN hs)

/-- On a cut-edge split of the induced network, each alternative has concordance factor
`(1 - p_ab|cd) / 2`: the alternatives are equal, and the three sum to one. -/
theorem nmscCF_alternative_eq (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {s : QuartetTree X} (hs : InducedCutSplit N s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ ρ r = (1 - nmscCF N θ ρ s) / 2 := by
  have hsum := NMSC.sum_nmscCF_weak (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 s.card_taxa
  rw [← add_sum_erase _ _ (mem_treesOn.2 rfl : s ∈ treesOn s.taxa), ← s.alternatives_eq,
    sum_congr rfl (cut_alternatives_weak hN hθ hρ s hs · · r hr), sum_const,
    s.card_alternatives] at hsum
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith

/-- On a cut-edge split, (3.1) is `1/3 < p_ab|cd`. -/
theorem nmscCF_lt_iff_one_third_lt (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {s : QuartetTree X} (hs : InducedCutSplit N s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ ρ r < nmscCF N θ ρ s ↔ 1 / 3 < nmscCF N θ ρ s := by
  rw [nmscCF_alternative_eq hN hθ hρ hs hr]
  constructor <;> intro h <;> linarith

/-- On a cut-edge split, the absence of an anomaly in the sense of Definition 2 of Ané et al. 2024
(`p_ab|cd < 1/3`) is the weak form of (3.1). -/
theorem nmscCF_le_iff_one_third_le (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {s : QuartetTree X} (hs : InducedCutSplit N s) {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    nmscCF N θ ρ r ≤ nmscCF N θ ρ s ↔ 1 / 3 ≤ nmscCF N θ ρ s := by
  rw [nmscCF_alternative_eq hN hθ hρ hs hr]
  constructor <;> intro h <;> linarith

/-- **Remark 3.3** (`ecto:rem3_3`), first claim. The NMSC with inheritance correlation `0 ≤ ρ ≤ 1` satisfies the
assumptions of Theorem 3.1, provided the quartet tree of each cut edge is strictly the most probable; cut edges
have positive lengths under `IsMetric`.

Equation (3.1) is the assumption, so "no anomalous quartets" must be read in this strict form, as
`TOBQMC.IsTQuartetNonanomalous` and `NoAnomalousQuartets` do. Definition 2 of the cited [8] (Ané et al.
2024) calls a quartet anomalous when `p_ab|cd < 1/3`, so that its absence is only `1/3 ≤ p_ab|cd`
(`nmscCF_le_iff_one_third_le`), and (3.1) can fail with it: by Example 1 of [8], on the `3₂`-cycle with hybrid
arcs of length `0`, tree arc of length `s₀` in the cycle and cut edge of length `t`,
`p_ab|cd = 1/3 + (2/3)(1 - e^{-t}) - (2/3) e^{-t} (1 - ρ) γ₁ γ₂ (1 - e^{-s₀})`, which is `1/3` for the positive
length `t = log (1 + (1 - ρ) γ₁ γ₂ (1 - e^{-s₀}))`, for any `ρ < 1`. There all three concordance factors are `1/3`,
the network is not anomalous in the sense of [8], its cut edge has positive length, (3.1) fails, and so does the
conclusion of Theorem 3.1: on these four taxa all three resolved trees are optimal. ([8] is C. Ané, J. Fogg,
E. Allman, H. Baños, J. Rhodes, J. Math. Biol. 88 (2024), read in the preprint bioRxiv 10.1101/2023.08.18.553582.) -/
theorem remark3_3_nmsc (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hano : TOBQMC.IsTQuartetNonanomalous N (nmscCF N θ ρ)) :
    Theorem31Assumptions N (nmscCF N θ ρ) :=
  ⟨fun s => (nmscCF_pos hN hθ hρ s).le, hano, NMSC.exchangeability hN hθ hρ⟩

/-- **Remark 3.3** (`ecto:rem3_3`), second claim, for the NMSC with common inheritance `ρ = 1`. Equation (3.1) holds
provided only that cut edges have positive lengths. Other tree arcs may have length zero, and any hybrid arc may
have length or inheritance zero. Condition 2 holds for all such parameters. -/
theorem remark3_3_common (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hcut : ∀ e, N.graph.underlying.IsBridge e → 0 < θ.length e) : Theorem31Assumptions N (nmscCF N θ 1) :=
  ⟨NMSC.nmscCF_nonneg_weak hN hθ ⟨zero_le_one, le_rfl⟩,
    fun _ hs _ hr => nmscCF_lt_rho_one_of_displays hN hθ hcut hs hr,
    exchangeability_weak hN hθ ⟨zero_le_one, le_rfl⟩⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- A cut edge is a tree arc. -/
theorem isTreeArc_of_isBridge (hN : N.IsPhylogenetic) {e : E} (he : N.graph.underlying.IsBridge e) : N.IsTreeArc e := by
  rcases NMSC.isTreeArc_or_isHybridArc (N := N) e with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h
    by_cases hae : a = e
    · have hb' : N.graph.target b = N.graph.target e := hb
      exact not_isBridge_of_two_parents hN (hae ▸ hab) hb'.symm he
    · exact not_isBridge_of_two_parents hN (Ne.symm hae) ha.symm he

/-- Valid parameters at `ρ = 1`: there are no anomalous quartets, and the assumptions of Theorem 3.1 hold. -/
theorem remark3_3_common_of_isMetric (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) :
    Theorem31Assumptions N (nmscCF N θ 1) :=
  remark3_3_common hN hθ.isWeakMetric fun e he => hθ.1 e (isTreeArc_of_isBridge hN he)

/-- The forward direction of Assumption 1 for the NMSC with common inheritance holds with no assumption on
the parameters: `nmscCF_lt_rho_one` replaces the assumption of no anomalous quartets in Proposition 5.1. -/
theorem assumption1Forward_common (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) :
    Assumption1Forward N (nmscCF N θ 1) :=
  ⟨fun q hq ht => NMSC.trivial_uniform hN hθ ⟨zero_le_one, le_rfl⟩ q hq ht,
    fun _ hs => ⟨fun _ hr => nmscCF_lt_rho_one hN hθ hs hr,
      NMSC.cut_alternatives hN hθ ⟨zero_le_one, le_rfl⟩ _ hs⟩⟩

/-! ### The law of unrooted gene trees under the NMSC -/

variable (N θ ρ) in
/-- The law of the unrooted gene trees under the NMSC. -/
def nmscTreeDist : UnrootedGeneTree X → ℝ := imageTreeDist (geneTreeDist N θ ρ) unroot

/-- A gene tree of positive probability is a binary rooted tree on the taxa. -/
theorem isUnrootedTree_of_geneTreeDist_ne_zero [Nonempty X] (hN : N.IsPhylogenetic)
    {G : Finset (Finset X)} (hG : geneTreeDist N θ ρ G ≠ 0) : IsUnrootedTree (unroot G) :=
  ⟨G, (geneTreeDist_support hN hG).1, rfl⟩

/-- The law of the unrooted gene trees is a probability distribution. -/
theorem nmscTreeDist_isDist [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    (∀ G, 0 ≤ nmscTreeDist N θ ρ G) ∧ ∑ G, nmscTreeDist N θ ρ G = 1 :=
  ⟨imageTreeDist_nonneg (NMSC.geneTreeDist_nonneg_weak hN hθ hρ) _,
    (sum_imageTreeDist fun _ h => isUnrootedTree_of_geneTreeDist_ne_zero hN h).trans
      (NMSC.sum_geneTreeDist_weak hN hθ.isNormalized hρ.1)⟩

/-- Under the NMSC, gene trees are binary, so that no quartet is unresolved: the concordance factors of
`expectedCF` are those of `nmscCF`. -/
theorem expectedCF_nmscTreeDist [Nonempty X] (hN : N.IsPhylogenetic) (s : QuartetTree X) :
    expectedCF (nmscTreeDist N θ ρ) s = nmscCF N θ ρ s := by
  unfold nmscTreeDist nmscCF
  rw [expectedCF_imageTreeDist fun _ h => isUnrootedTree_of_geneTreeDist_ne_zero hN h]
  refine sum_congr rfl fun G _ => ?_
  by_cases hG : geneTreeDist N θ ρ G = 0
  · simp [hG]
  obtain ⟨hH, hbin⟩ := isBinaryHierarchy_iff_card_childClusters.1 (geneTreeDist_support hN hG)
  have hBT : IsBinaryTree (unroot G) := ⟨G, hH, rfl, hbin⟩
  obtain ⟨r₀, hr₀, hdisp⟩ := hBT.exists_displays s.card_taxa
  unfold geneContribution
  by_cases hd : Displays (unroot G) s
  · simp [hd]
  · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right fun h => h r₀ hr₀ hdisp, mul_zero]

/-- **Corollary 3.6** (`ecto:cor3_6`) for the NMSC with inheritance correlation `0 ≤ ρ ≤ 1` and no anomalous
quartets. -/
theorem corollary3_6_nmsc [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hano : TOBQMC.IsTQuartetNonanomalous N (nmscCF N θ ρ)) :
    Tendsto (fun n => iidProb (nmscTreeDist N θ ρ) n fun ω =>
      ∀ T, IsUnrootedTree T →
        (∀ T', IsUnrootedTree T' → quartetSupport (empiricalCF ω) T' ≤ quartetSupport (empiricalCF ω) T) →
        treeOfBlobs N ⊆ T) atTop (𝓝 1) := by
  have hexp : expectedCF (nmscTreeDist N θ ρ) = nmscCF N θ ρ := funext (expectedCF_nmscTreeDist hN)
  have h := remark3_3_nmsc hN hθ hρ hano
  rw [← hexp] at h
  exact corollary3_6 hN _ (nmscTreeDist_isDist hN hθ.isWeakMetric hρ) h.cut h.exchangeable

/-- **Corollary 3.6** (`ecto:cor3_6`) for the NMSC with common inheritance, with positive lengths on cut edges. -/
theorem corollary3_6_common [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hcut : ∀ e, N.graph.underlying.IsBridge e → 0 < θ.length e) :
    Tendsto (fun n => iidProb (nmscTreeDist N θ 1) n fun ω =>
      ∀ T, IsUnrootedTree T →
        (∀ T', IsUnrootedTree T' → quartetSupport (empiricalCF ω) T' ≤ quartetSupport (empiricalCF ω) T) →
        treeOfBlobs N ⊆ T) atTop (𝓝 1) := by
  have hexp : expectedCF (nmscTreeDist N θ 1) = nmscCF N θ 1 := funext (expectedCF_nmscTreeDist hN)
  have h := remark3_3_common hN hθ hcut
  rw [← hexp] at h
  exact corollary3_6 hN _ (nmscTreeDist_isDist hN hθ ⟨zero_le_one, le_rfl⟩) h.cut h.exchangeable

end NMSC

/-! ### The displayed tree model -/

section Displayed

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E}

variable (N θ) in
/-- **The displayed tree model** (ECToBlob §2, with no coalescent process): a parent is chosen at each vertex,
with probability the product of the inheritance values, and the gene tree is the tree on the taxa that the
choice displays. A gene tree may have polytomies, from the multifurcations of the network. -/
def displayedTreeDist : UnrootedGeneTree X → ℝ := imageTreeDist (N.choiceWeight θ) N.displayedSides

variable (N θ) in
/-- The concordance factors of the displayed tree model, with the paper's convention of §2 for a star tree: an
unresolved quartet contributes `1/3` to each of the three quartet trees, as if each resolution of the polytomy
had probability `1/3` (lines 289-293 and 399-400). -/
def displayedCF : QuartetTree X → ℝ := expectedCF (displayedTreeDist N θ)

/-- The concordance factors of the displayed tree model as a sum over the parent choices. -/
theorem displayedCF_eq [Nonempty X] (hN : N.IsPhylogenetic) (s : QuartetTree X) :
    displayedCF N θ s = ∑ c : N.ParentChoice, N.choiceWeight θ c * geneContribution (N.displayedSides c) s :=
  expectedCF_imageTreeDist (fun c _ => isUnrootedTree_displayedSides hN c) s

/-- **The law of the displayed trees is a probability distribution.** -/
theorem displayedTreeDist_isDist [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) :
    (∀ G, 0 ≤ displayedTreeDist N θ G) ∧ ∑ G, displayedTreeDist N θ G = 1 :=
  ⟨imageTreeDist_nonneg (choiceWeight_nonneg hθ) _,
    (sum_imageTreeDist fun c _ => isUnrootedTree_displayedSides hN c).trans
      (sum_choiceWeight hN hθ.isNormalized)⟩

/-- **On a cut-edge split `ab|cd` of the induced network, `p_ab|cd = 1`.** Every displayed tree displays it. -/
theorem displayedCF_of_inducedCutSplit [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
    {s : QuartetTree X} (hs : InducedCutSplit N s) :
    displayedCF N θ s = 1 ∧ ∀ r ∈ s.alternatives, displayedCF N θ r = 0 := by
  have h := fun c : N.ParentChoice => geneContribution_of_displays (isUnrootedTree_displayedSides hN c)
    (displays_displayedSides_of_inducedCutSplit hN c hs)
  refine ⟨?_, fun r hr => ?_⟩
  · rw [displayedCF_eq hN, sum_congr rfl fun c _ => by rw [(h c).1, mul_one]]
    exact sum_choiceWeight hN hθ
  · rw [displayedCF_eq hN]
    exact sum_eq_zero fun c _ => by rw [(h c).2 r hr, mul_zero]

/-- The concordance factors of the displayed tree model sum to one on each set of four taxa, as the convention for
star trees intends. -/
theorem sum_displayedCF [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) {q : Finset X}
    (hq : q.card = 4) : ∑ r ∈ treesOn q, displayedCF N θ r = 1 := by
  simp only [displayedCF_eq hN]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_geneContribution (isUnrootedTree_displayedSides hN _) hq, mul_one]
  exact sum_choiceWeight hN hθ

/-! ### The displayed tree model as a limit of common inheritance -/

/-- The concordance factors of the displayed tree model only see the inheritance. -/
theorem displayedCF_congr {θ θ' : MetricData E} (h : θ.inheritance = θ'.inheritance) :
    displayedCF N θ = displayedCF N θ' := by
  have hw : N.choiceWeight θ = N.choiceWeight θ' := by
    funext c
    simp only [choiceWeight, h]
  unfold displayedCF displayedTreeDist
  rw [hw]

/-- **The displayed tree model is the limit of the NMSC with common inheritance, as all lengths grow**, at the
rate of the shortest arc. On a set of taxa that a displayed tree leaves unresolved, the coalescent gives `1/3` to
each quartet tree, for all lengths: this is the paper's convention for the displayed tree model, in §2. -/
theorem abs_nmscCF_sub_displayedCF_le [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {m : ℝ}
    (hm : 0 < m) (hℓ : ∀ f, m ≤ θ.length f) (s : QuartetTree X) :
    |nmscCF N θ 1 s - displayedCF N θ s| ≤ Real.exp (-m) := by
  have hpos : ∀ f, 0 < θ.length f := fun f => lt_of_lt_of_le hm (hℓ f)
  have hterm : ∀ c : N.ParentChoice, |nmscCF N (N.choiceMetric θ c) 1 s -
      geneContribution (N.displayedSides c) s| ≤ Real.exp (-m) := by
    intro c
    have hT := isUnrootedTree_displayedSides hN c
    have hexp := Real.exp_pos (-m)
    by_cases hd : Displays (N.displayedSides c) s
    · obtain ⟨h1, h2, -⟩ := nmscCF_choiceMetric_bounds_of_displays hN c hm hℓ hd
      rw [(geneContribution_of_displays hT hd).1, abs_le]
      constructor <;> linarith
    by_cases hex : ∃ r ∈ treesOn s.taxa, Displays (N.displayedSides c) r
    · obtain ⟨r, hr, hdr⟩ := hex
      have hsr : s ∈ r.alternatives := QuartetTree.mem_alternatives.2
        ⟨(mem_treesOn.1 hr).symm, fun h => hd (h ▸ hdr)⟩
      have h3 := (nmscCF_choiceMetric_bounds_of_displays hN c hm hℓ hdr).2.2 s hsr
      have h0 := NMSC.nmscCF_nonneg_weak (ρ := 1) hN
        (isWeakMetric_choiceMetric hN (fun f => (hpos f).le) c) ⟨zero_le_one, le_rfl⟩ s
      rw [(geneContribution_of_displays hT hdr).2 s hsr, sub_zero, abs_of_nonneg h0]
      exact h3
    · push Not at hex
      have hthird := nmscCF_choiceMetric_eq_third hN c hpos s.card_taxa hex (mem_treesOn.2 rfl)
      have hc : geneContribution (N.displayedSides c) s = 1 / 3 := by
        unfold geneContribution
        rw [ite_eq_right hd, ite_eq_left hex]
      rw [hthird, hc, sub_self, abs_zero]
      exact hexp.le
  rw [nmscCF_rho_one hN hθ.isNormalized s, displayedCF_eq hN, ← sum_sub_distrib]
  simp only [← mul_sub]
  calc |∑ c : N.ParentChoice, N.choiceWeight θ c * (nmscCF N (N.choiceMetric θ c) 1 s -
        geneContribution (N.displayedSides c) s)|
      ≤ ∑ c : N.ParentChoice, |N.choiceWeight θ c * (nmscCF N (N.choiceMetric θ c) 1 s -
        geneContribution (N.displayedSides c) s)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : N.ParentChoice, N.choiceWeight θ c * Real.exp (-m) := sum_le_sum fun c _ => by
        rw [abs_mul, abs_of_nonneg (choiceWeight_nonneg hθ c)]
        exact mul_le_mul_of_nonneg_left (hterm c) (choiceWeight_nonneg hθ c)
    _ = Real.exp (-m) := by
        rw [← Finset.sum_mul, sum_choiceWeight hN hθ.isNormalized, one_mul]

/-- The displayed tree model is the limit of the NMSC with common inheritance, as all lengths grow. -/
theorem tendsto_nmscCF_addLength_displayedCF [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (s : QuartetTree X) :
    Tendsto (fun L : ℝ => nmscCF N (addLength θ L) 1 s) atTop (𝓝 (displayedCF N θ s)) := by
  have hcongr : ∀ L : ℝ, displayedCF N (addLength θ L) = displayedCF N θ := fun L =>
    displayedCF_congr rfl
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hw : N.IsWeakMetric (addLength θ L) := ⟨fun f => add_nonneg (hθ.1 f) hL.le, hθ.2.1, hθ.2.2⟩
  have := abs_nmscCF_sub_displayedCF_le hN hw hL (fun f => le_add_of_nonneg_left (hθ.1 f)) s
  rwa [hcongr, ← Real.norm_eq_abs] at this

/-- **Remark 3.3** (`ecto:rem3_3`), third claim, for the displayed tree model. No assumption on lengths is needed:
the gene trees are topological, and a cut edge is on every displayed tree. Only the inheritance values matter, as
a probability distribution at each reticulation; condition 2 follows, since a side of the tree of blobs is on every
displayed tree. -/
theorem remark3_3_displayed [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) :
    Theorem31Assumptions N (displayedCF N θ) := by
  refine ⟨fun s => ?_, fun s hs r hr => ?_, ?_⟩
  · refine sum_nonneg fun G _ => mul_nonneg ((displayedTreeDist_isDist hN hθ).1 G) ?_
    unfold geneContribution
    split_ifs <;> norm_num
  · obtain ⟨h1, h0⟩ := displayedCF_of_inducedCutSplit hN hθ.isNormalized
      (inducedCutSplit_of_displays_treeOfBlobs hN hs)
    rw [h1, h0 r hr]
    exact zero_lt_one
  · rintro s s' a a' has ha's hs' ⟨A, hA, haA, ha'A, hdis⟩
    have hoth : ∀ x ∈ s.taxa, x ≠ a → x ∉ A := fun x hx hxa hxA =>
      disjoint_left.1 hdis hxA (mem_erase.2 ⟨hxa, hx⟩)
    obtain ⟨y, hy, hya⟩ := exists_mem_ne (by rw [s.card_taxa]; omega : 1 < s.taxa.card) a
    have hAT : A ∈ treeOfBlobs N := mem_filter.2 ⟨mem_univ _, ⟨a, haA⟩, ⟨y, mem_compl.2 (hoth y hy hya)⟩, hA⟩
    rw [displayedCF_eq hN, displayedCF_eq hN]
    refine sum_congr rfl fun c _ => ?_
    rw [geneContribution_eq_of_replace (isUnrootedTree_displayedSides hN c)
      (treeOfBlobs_subset_displayedSides hN c hAT) haA ha'A has ha's hoth hs']

/-- **Remark 3.2** (`ecto:rem3_2`) for the displayed tree model, with the convention for star trees: the optimal
trees are binary. -/
theorem isBinaryTree_of_displayedCF_maximizer [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hmax : ∀ T', IsUnrootedTree T' → quartetSupport (displayedCF N θ) T' ≤ quartetSupport (displayedCF N θ) T) :
    IsBinaryTree T :=
  remark3_2 _ (remark3_3_displayed hN hθ).nonneg (fun _ hq => sum_displayedCF hN hθ.isNormalized hq) hT hmax

/-! ### Remark 3.2 and the polytomies of the network

Lines 397-398: "For the displayed tree model, this is not the case, as resolving a polytomy on T arising from one in the
network will have no impact on T's MQS score." The sentence is about the concordance factors of lines 278-284, the
probabilities of the resolved gene tree topologies, on which a star tree counts for nothing (`displayedRawCF`). Under the
convention of lines 289-293, where a star tree contributes `(1/3, 1/3, 1/3)` (`displayedCF`), resolving adds `1/3` for each
new quartet tree (`quartetScore_displayedCF_of_resolution`): this is line 400 (`isBinaryTree_of_displayedCF_maximizer`). -/

variable (N θ) in
/-- The concordance factors of the displayed tree model of lines 278-284: the probabilities of the resolved gene tree
topologies, which may sum to less than one. -/
def displayedRawCF : QuartetTree X → ℝ := displayCF (displayedTreeDist N θ) Subtype.val

/-- The concordance factors of the displayed tree model of lines 278-284, as a sum over the parent choices. -/
theorem displayedRawCF_eq [Nonempty X] (hN : N.IsPhylogenetic) (s : QuartetTree X) :
    displayedRawCF N θ s =
      ∑ c : N.ParentChoice, N.choiceWeight θ c * if Displays (N.displayedSides c) s then 1 else 0 := by
  have h := sum_imageTreeDist_mul (w := N.choiceWeight θ) (g := N.displayedSides)
    (fun c _ => isUnrootedTree_displayedSides hN c) (fun T => if Displays T s then 1 else 0)
  rw [← h]
  unfold displayedRawCF displayCF displayedTreeDist
  refine sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

/-- **On a trivial 4-blob the concordance factors of lines 278-284 vanish.** -/
theorem displayedRawCF_of_hasTrivialFourBlob [Nonempty X] (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (ht : HasTrivialFourBlob N s.taxa) : displayedRawCF N θ s = 0 := by
  rw [displayedRawCF_eq hN]
  refine sum_eq_zero fun c _ => ?_
  rw [ite_eq_right (not_displays_of_hasTrivialFourBlob hN c s.card_taxa ht (mem_treesOn.2 rfl)), mul_zero]

/-- **On a trivial 4-blob the concordance factors of the convention of lines 289-293 are `1/3`.** -/
theorem displayedCF_of_hasTrivialFourBlob [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
    {s : QuartetTree X} (ht : HasTrivialFourBlob N s.taxa) : displayedCF N θ s = 1 / 3 := by
  rw [displayedCF_eq hN]
  have hc : ∀ c : N.ParentChoice, geneContribution (N.displayedSides c) s = 1 / 3 := fun c => by
    unfold geneContribution
    rw [ite_eq_right (not_displays_of_hasTrivialFourBlob hN c s.card_taxa ht (mem_treesOn.2 rfl)), ite_eq_left]
    exact fun r hr => not_displays_of_hasTrivialFourBlob hN c s.card_taxa ht hr
  simp only [hc]
  rw [← Finset.sum_mul, sum_choiceWeight hN hθ, one_mul]

/-- **Remark 3.2** (`ecto:rem3_2`), lines 397-398, in the reading of lines 278-284: **resolving polytomies of `T` that arise
from the network has no impact on the score.** `T'` resolves `T`, and the quartet trees that it displays and `T` does not
are on trivial 4-blobs. So a maximizer of this score need not be binary. -/
theorem quartetScore_displayedRawCF_of_resolution [Nonempty X] (hN : N.IsPhylogenetic)
    {T T' : Finset (Finset X)} (hT : T ⊆ T')
    (hnew : ∀ s, Displays T' s → ¬ Displays T s → HasTrivialFourBlob N s.taxa) :
    quartetSupport (displayedRawCF N θ) T' = quartetSupport (displayedRawCF N θ) T := by
  refine sum_congr rfl fun s _ => ?_
  by_cases hd : Displays T s
  · rw [ite_eq_left hd, ite_eq_left (hd.mono hT)]
  · rw [ite_eq_right hd]
    split_ifs with hd'
    · exact displayedRawCF_of_hasTrivialFourBlob hN (hnew s hd' hd)
    · rfl

/-- **Remark 3.2** (`ecto:rem3_2`), lines 397-398, for all polytomies: if every set of four taxa in distinct blocks of a
multifurcation of `T` is a trivial 4-blob of the network, then any resolution of `T` has the score of `T`. -/
theorem remark3_2_no_impact [Nonempty X] (hN : N.IsPhylogenetic) {T T' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hT' : IsUnrootedTree T') (hsub : T ⊆ T')
    (hP : ∀ P ∈ multifurcations T, ∀ q : Finset X, #q = 4 → InDistinctBlocks P q → HasTrivialFourBlob N q) :
    quartetSupport (displayedRawCF N θ) T' = quartetSupport (displayedRawCF N θ) T := by
  refine quartetScore_displayedRawCF_of_resolution hN hsub fun s hd' hd => ?_
  have hstar : ∀ r ∈ treesOn s.taxa, ¬ Displays T r := fun r hr hdr => hd (by
    have := hT'.displays_unique (hdr.mono hsub) hd' (mem_treesOn.1 hr)
    rwa [this] at hdr)
  obtain ⟨P, ⟨hPm, hI⟩, -⟩ := existsUnique_center hT s.card_taxa hstar
  exact hP P hPm _ s.card_taxa hI

/-- Under the convention of lines 289-293, each new quartet tree adds `1/3`: the opposite of "no impact", and the reason
for line 400. -/
theorem quartetScore_displayedCF_of_resolution [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
    {T T' : Finset (Finset X)} (hT : T ⊆ T')
    (hnew : ∀ s, Displays T' s → ¬ Displays T s → HasTrivialFourBlob N s.taxa) :
    quartetSupport (displayedCF N θ) T' = quartetSupport (displayedCF N θ) T +
      (#(univ.filter fun s => Displays T' s ∧ ¬ Displays T s) : ℝ) * (1 / 3) := by
  unfold quartetSupport
  rw [← nsmul_eq_mul, ← sum_const, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  by_cases hd : Displays T s
  · simp [hd, hd.mono hT]
  · by_cases hd' : Displays T' s
    · simp [hd, hd', displayedCF_of_hasTrivialFourBlob hN hθ (hnew s hd' hd)]
    · simp [hd, hd']

/-! ### Counts and p-values on a trivial 4-blob

Under the convention of lines 289-293 the counts on a trivial 4-blob are `(n/3, n/3, n/3)` on every sample, so the star and
T1 p-values are `1`: they are not asymptotically uniform, as lines 1019-1020 and the proof of Theorem 8.2 at line 1065 say,
and Lemma 8.1 does not apply (line 1076). -/

/-- The quartet counts of a sample of gene trees under the convention of lines 289-293. -/
def conventionCount {n : ℕ} (ω : Fin n → UnrootedGeneTree X) (s : QuartetTree X) : ℝ :=
  ∑ i, geneContribution (ω i).val s

/-- **The counts on a trivial 4-blob are deterministic.** -/
theorem conventionCount_of_hasTrivialFourBlob [Nonempty X] (hN : N.IsPhylogenetic) {q : Finset X}
    (hq : #q = 4) (ht : HasTrivialFourBlob N q) {n : ℕ} {ω : Fin n → UnrootedGeneTree X}
    (hω : ∀ i, displayedTreeDist N θ (ω i) ≠ 0) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    conventionCount ω r = n / 3 := by
  have hterm : ∀ i, geneContribution (ω i).val r = 1 / 3 := by
    intro i
    obtain ⟨c, -, hc⟩ := exists_ne_zero_of_sum_ne_zero (hω i)
    have hsides : N.displayedSides c = (ω i).val := by
      by_contra hne
      exact hc (ite_eq_right hne)
    have hnot : ∀ r' ∈ treesOn q, ¬ Displays (ω i).val r' := fun r' hr' => by
      rw [← hsides]
      exact not_displays_of_hasTrivialFourBlob hN c hq ht hr'
    unfold geneContribution
    rw [ite_eq_right (hnot r hr), ite_eq_left]
    rw [mem_treesOn.1 hr]
    exact hnot
  unfold conventionCount
  simp only [hterm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Equal counts on the trees on `q`: the star statistics vanish. -/
theorem starPValue_of_const (k : StarTest) {c : QuartetTree X → ℝ} {q : Finset X} (hq : #q = 4) {m : ℝ}
    (hc : ∀ r ∈ treesOn q, c r = m) : starPValue k c q = 1 := by
  have h3 : #(treesOn q) = 3 := card_treesOn hq
  have hsum : ∑ t ∈ treesOn q, c t = 3 * m := by
    rw [sum_congr rfl hc, sum_const, h3]
    simp
  cases k with
  | lrt =>
    have hstat : starStat c q = 0 := by
      unfold starStat
      rw [hsum, sum_congr rfl fun r hr => by rw [hc r hr], sum_const, h3]
      have : 3 * m / 3 = m := by ring
      rw [this]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    simp [starPValue, hstat, chiSqTwoTail]
  | pearson =>
    have hstat : pearsonStat c q = 0 := by
      unfold pearsonStat
      refine sum_eq_zero fun r hr => ?_
      rw [hsum, hc r hr]
      have : m - 3 * m / 3 = 0 := by ring
      rw [this]
      simp
    simp [starPValue, hstat, chiSqTwoTail]

/-- Equal counts on the trees on the taxa of `s`: the T1 statistic vanishes, and the p-value is `1`. -/
theorem t1PValue_of_const {c : QuartetTree X → ℝ} {s : QuartetTree X} {m : ℝ}
    (hc : ∀ r ∈ treesOn s.taxa, c r = m) : t1PValue c s = 1 := by
  have halt : ∀ r ∈ s.alternatives, c r = m := fun r hr =>
    hc r (mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1)
  have hms : c s = m := hc s (mem_treesOn.2 rfl)
  have hsum : ∑ r ∈ s.alternatives, c r = 2 * m := by
    rw [sum_congr rfl halt, sum_const, s.card_alternatives]
    simp
  have hstat : t1Stat c s = 0 := by
    unfold t1Stat
    rw [ite_eq_left (by rw [hsum, hms]; linarith)]
    unfold lineStat
    rw [hsum, sum_congr rfl fun r hr => by rw [halt r hr], sum_const, s.card_alternatives]
    by_cases hm : m = 0
    · simp [hm]
    · rw [Real.log_mul (by norm_num) hm]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
  unfold t1PValue
  rw [hstat]
  refine le_antisymm (Trinomial.t1Tail_le_one _ _) ?_
  have hle := QuartetTests.chiSqOneTail_le_t1Tail
    (muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r)) 0
  rwa [Trinomial.chiSqOneTail_zero] at hle

/-- **The star and T1 p-values on a trivial 4-blob are `1`, on every sample of the displayed tree model.** -/
theorem pValues_of_hasTrivialFourBlob [Nonempty X] (hN : N.IsPhylogenetic) {q : Finset X}
    (hq : #q = 4) (ht : HasTrivialFourBlob N q) {n : ℕ} {ω : Fin n → UnrootedGeneTree X}
    (hω : ∀ i, displayedTreeDist N θ (ω i) ≠ 0) (k : StarTest) :
    starPValue k (conventionCount ω) q = 1 ∧
      ∀ s ∈ treesOn q, t1PValue (conventionCount ω) s = 1 := by
  have hc := fun r hr => conventionCount_of_hasTrivialFourBlob (θ := θ) hN hq ht hω (r := r) hr
  refine ⟨starPValue_of_const k hq hc, fun s hs => t1PValue_of_const (m := n / 3) fun r hr => ?_⟩
  rw [mem_treesOn.1 hs] at hr
  exact hc r hr

/-- **The star p-value on a trivial 4-blob of the displayed tree model is not asymptotically uniform**, so the
hypothesis of Lemma 8.1 fails, and with it the sentence "each individual p-value is uniformly distributed" in the proof of
Theorem 8.2 (line 1065), which says "any model" at line 1042. -/
theorem not_asymptoticallyUniform_starPValue [Nonempty X] (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4)
    (ht : HasTrivialFourBlob N q) (k : StarTest) :
    ¬ QuartetTests.AsymptoticallyUniform (displayedTreeDist N θ)
      (fun _ ω => starPValue k (conventionCount ω) q) := by
  intro h
  have hzero : ∀ n, iidProb (displayedTreeDist N θ) n
      (fun ω : Fin n → UnrootedGeneTree X => starPValue k (conventionCount ω) q ≤ 1 / 2) = 0 := by
    intro n
    refine sum_eq_zero fun ω _ => ?_
    split_ifs with hle
    · refine prod_eq_zero_iff.2 ?_
      by_contra hcon
      push Not at hcon
      have hp := (pValues_of_hasTrivialFourBlob (θ := θ) hN hq ht (ω := ω) (fun i => hcon i (mem_univ i)) k).1
      have hle' : starPValue k (conventionCount ω) q ≤ 1 / 2 := hle
      rw [hp] at hle'
      norm_num at hle'
    · rfl
  have hlim := h (1 / 2) (by norm_num) (by norm_num)
  simp only [hzero] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at this

/-- **Corollary 3.6** (`ecto:cor3_6`) for the displayed tree model. -/
theorem corollary3_6_displayed [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) :
    Tendsto (fun n => iidProb (displayedTreeDist N θ) n fun ω =>
      ∀ T, IsUnrootedTree T →
        (∀ T', IsUnrootedTree T' → quartetSupport (empiricalCF ω) T' ≤ quartetSupport (empiricalCF ω) T) →
        treeOfBlobs N ⊆ T) atTop (𝓝 1) :=
  corollary3_6 hN _ (displayedTreeDist_isDist hN hθ) (remark3_3_displayed hN hθ).cut
    (remark3_3_displayed hN hθ).exchangeable

end Displayed

/-! ### Condition 2: the induced network

The first half of condition 2 as printed: `p_xy|zw` is determined by the network induced on `x, y, z, w`. -/

section Induced

variable [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}

/-- **Remark 3.3** (`ecto:rem3_3`), the NMSC and the first half of condition 2 as printed: a concordance factor is
that of the network induced on the four taxa, for every `ρ` (`NMSC.nmscCF_inducedNetwork`). -/
theorem remark3_3_induced_nmsc (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {Q : Finset X} (hQ : #Q = 4) (hY : (Q : Set X).Nontrivial) [Fintype (Q : Set X)]
    [DecidableEq (Q : Set X)]
    [Fintype {v // ¬ (lsaNetwork hN (Q : Set X) hY.nonempty).IsChainVertex v}]
    [Fintype {e // ¬ (lsaNetwork hN (Q : Set X) hY.nonempty).IsChainVertex
      ((lsaNetwork hN (Q : Set X) hY.nonempty).graph.source e)}]
    (s : QuartetTree (Q : Set X)) :
    nmscCF N θ ρ (s.map Subtype.val_injective) =
      nmscCF (inducedNetwork hN (Q : Set X) hY) (inducedMetric hN (Q : Set X) hY.nonempty θ) ρ s :=
  (NMSC.nmscCF_inducedNetwork hN hθ hρ hQ hY s).symm

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The lengths on the induced network are at least those on the network: a length is a sum along a chain. -/
theorem le_inducedMetric_length {Y : Set X} (hN : N.IsPhylogenetic) (hY : Y.Nonempty) {m : ℝ} (hm : 0 ≤ m)
    (hℓ : ∀ f, m ≤ θ.length f) (e) : m ≤ (inducedMetric hN Y hY θ).length e := by
  let _ : Fintype (N.belowArcs (lsa hN Y hY) Y) := Fintype.ofFinite _
  refine (hℓ e.val.val).trans ?_
  refine Finset.single_le_sum (f := fun f : N.belowArcs (lsa hN Y hY) Y => θ.length f.val)
    (fun f _ => hm.trans (hℓ f.val)) (mem_filter.2 ⟨mem_univ _, Or.inl rfl⟩)

/-- **Remark 3.3** (`ecto:rem3_3`), the displayed tree model and the first half of condition 2 as printed: a
concordance factor is that of the network induced on the four taxa. Both sides are limits of the concordance
factors under common inheritance, as all lengths grow (`abs_nmscCF_sub_displayedCF_le`), and these agree
(`NMSC.nmscCF_inducedNetwork`). -/
theorem remark3_3_induced_displayed (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    {Q : Finset X} (hQ : #Q = 4) (hY : (Q : Set X).Nontrivial) [Fintype (Q : Set X)]
    [DecidableEq (Q : Set X)]
    [Fintype {v // ¬ (lsaNetwork hN (Q : Set X) hY.nonempty).IsChainVertex v}]
    [Fintype {e // ¬ (lsaNetwork hN (Q : Set X) hY.nonempty).IsChainVertex
      ((lsaNetwork hN (Q : Set X) hY.nonempty).graph.source e)}]
    (s : QuartetTree (Q : Set X)) :
    displayedCF N θ (s.map Subtype.val_injective) =
      displayedCF (inducedNetwork hN (Q : Set X) hY) (inducedMetric hN (Q : Set X) hY.nonempty θ) s := by
  have : Nonempty X := ⟨hY.nonempty.choose⟩
  have : Nonempty (Q : Set X) := hY.nonempty.to_subtype
  have hind := inducedNetwork_isPhylogenetic hN hY
  set D := displayedCF N θ (s.map Subtype.val_injective) with hD
  set D' := displayedCF (inducedNetwork hN (Q : Set X) hY) (inducedMetric hN (Q : Set X) hY.nonempty θ) s
    with hD'
  have hbound : ∀ L : ℝ, 0 < L → |D - D'| ≤ 2 * Real.exp (-L) := by
    intro L hL
    have hθL : N.IsMetric (addLength θ L) :=
      ⟨fun f hf => add_pos_of_nonneg_of_pos (NMSC.length_nonneg hθ f) hL,
        fun f _ => add_nonneg (NMSC.length_nonneg hθ f) hL.le, hθ.2.2.1, hθ.2.2.2.1, hθ.2.2.2.2⟩
    have hle : ∀ f, L ≤ (addLength θ L).length f := fun f =>
      le_add_of_nonneg_left (NMSC.length_nonneg hθ f)
    have hμ := isMetric_inducedMetric hN hY hθL
    have h₁ := abs_nmscCF_sub_displayedCF_le hN hθL.isWeakMetric hL hle (s.map Subtype.val_injective)
    have h₂ := abs_nmscCF_sub_displayedCF_le hind hμ.isWeakMetric hL
      (le_inducedMetric_length hN hY.nonempty hL.le hle) s
    have e₁ : displayedCF N (addLength θ L) = displayedCF N θ := displayedCF_congr rfl
    have e₂ : displayedCF (inducedNetwork hN (Q : Set X) hY)
        (inducedMetric hN (Q : Set X) hY.nonempty (addLength θ L)) =
        displayedCF (inducedNetwork hN (Q : Set X) hY) (inducedMetric hN (Q : Set X) hY.nonempty θ) :=
      displayedCF_congr rfl
    rw [e₁] at h₁
    rw [e₂, NMSC.nmscCF_inducedNetwork hN hθL ⟨zero_le_one, le_rfl⟩ hQ hY s] at h₂
    rw [abs_le] at h₁ h₂ ⊢
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hlim : Tendsto (fun L : ℝ => 2 * Real.exp (-L)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2
  have h0 : |D - D'| ≤ 0 := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hbound)
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end Induced

/-! ### Condition 2 as printed: pendant chains

The literal form of condition 2 is `PendantChainInvariant`. For the NMSC it comes down to where the lineages are. A
taxon whose pendant cut has the other three taxa on the side of the root (`IsDown`) goes up the chain as a single
lineage, to the attachment. If the three others are below the pendant cut (`IsUp`), then only what arrives at the
attachment from below matters (`cherryMass_placeInj_eq_of_below`). The hypothesis on the core arcs is not needed. -/

section Pendant

open PendantChain

variable {N : RootedNetwork V E X}

/-- The taxon `x` of `q` is below the arc `e`, and the other taxa of `q` are not. -/
def IsDown (N : RootedNetwork V E X) (q : Finset X) (x : X) (e : E) : Prop :=
  N.Dominates e x ∧ ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y

/-- The taxa of `q` other than `x` are below the arc `e`, and `x` is not. -/
def IsUp (N : RootedNetwork V E X) (q : Finset X) (x : X) (e : E) : Prop :=
  (∀ y ∈ q, y ≠ x → N.Dominates e y) ∧ ¬ N.IsBelow e x

omit [Fintype X] [DecidableEq X] in
/-- Along a path of the network induced on `Y` avoiding the pendant cut, the side does not change. -/
theorem mem_iff_mem_of_avoidingReach_induced {Y : Set X} {l : V} (hl : N.IsLeastStableAncestor Y l) {e : E}
    {S : Set V} (hcr : ∀ f ∈ inducedArcs N Y, N.graph.Crosses f S ↔ f = e) {a b : V}
    (hla : N.graph.Reaches l a) (h : N.AvoidingReach e a b) (hb : ∃ y ∈ Y, N.graph.Reaches b (N.leaf y)) :
    a ∈ S ↔ b ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | @tail c d hac hcd ih =>
    obtain ⟨g, hge, rfl, rfl⟩ := hcd
    obtain ⟨y, hy, hr⟩ := hb
    have hgI : g ∈ inducedArcs N Y := ⟨⟨y, hy, hr⟩, l, hl, hla.trans (AvoidingReach.reaches hac)⟩
    have hnc : ¬ N.graph.Crosses g S := fun h => hge ((hcr g hgI).1 h)
    exact (ih ⟨y, hy, Relation.ReflTransGen.head ⟨g, rfl, rfl⟩ hr⟩).trans (mem_iff_of_not_crosses hnc)

omit [Fintype X] [DecidableEq X] in
/-- A pendant cut goes one way or the other, and it describes the vertices of the induced network on its side. -/
theorem isPendantCut_cases [DecidableEq X] (hN : N.IsPhylogenetic) {q : Finset X} {x : X} (hx : x ∈ q) {e : E} {S : Set V}
    (h : IsPendantCut N (q : Set X) x e S) :
    (N.graph.source e ∉ S ∧ N.graph.target e ∈ S ∧ IsDown N q x e ∧
      ∀ u ∈ inducedVertices N (q : Set X), u ∈ S ↔ N.graph.Reaches (N.graph.target e) u) ∨
    (N.graph.source e ∈ S ∧ N.graph.target e ∉ S ∧ IsUp N q x e ∧
      ∀ u ∈ inducedVertices N (q : Set X), u ∈ S ↔ ¬ N.graph.Reaches (N.graph.target e) u) := by
  obtain ⟨heI, hcr, hleaf⟩ := h
  obtain ⟨⟨y₀, hy₀, hr₀⟩, l, hl, hls⟩ := heI
  have hA := hN.acyclic
  have hlt : N.graph.Reaches l (N.graph.target e) := hls.tail ⟨e, rfl, rfl⟩
  have hsrc : l ∈ S ↔ N.graph.source e ∈ S :=
    mem_iff_mem_of_avoidingReach_induced hl hcr .refl (avoidingReach_of_reaches_source hA hls .refl)
      ⟨y₀, hy₀, Relation.ReflTransGen.head ⟨e, rfl, rfl⟩ hr₀⟩
  have htgt : ∀ {b : V}, N.graph.Reaches (N.graph.target e) b → (∃ y ∈ (q : Set X), N.graph.Reaches b (N.leaf y)) →
      (N.graph.target e ∈ S ↔ b ∈ S) := fun hb hex =>
    mem_iff_mem_of_avoidingReach_induced hl hcr hlt (avoidingReach_of_target_reaches hA .refl hb) hex
  have hfroml : ∀ {y : X}, y ∈ (q : Set X) → N.AvoidingReach e N.root (N.leaf y) → (l ∈ S ↔ N.leaf y ∈ S) :=
    fun {y} hy hav => mem_iff_mem_of_avoidingReach_induced hl hcr .refl
      (hav.suffix_of_not_hasPathAvoiding (hl.1 y hy)) ⟨y, hy, .refl⟩
  have hside : ∀ u ∈ inducedVertices N (q : Set X),
      (N.graph.Reaches (N.graph.target e) u ∧ (N.graph.target e ∈ S ↔ u ∈ S)) ∨
        (¬ N.graph.Reaches (N.graph.target e) u ∧ (l ∈ S ↔ u ∈ S)) := by
    rintro u ⟨⟨l', hl', hlu⟩, z, hz, hzr⟩
    obtain rfl := hl.unique hN hl'
    by_cases hb : N.graph.Reaches (N.graph.target e) u
    · exact Or.inl ⟨hb, htgt hb ⟨z, hz, hzr⟩⟩
    · refine Or.inr ⟨hb, mem_iff_mem_of_avoidingReach_induced hl hcr .refl ?_ ⟨z, hz, hzr⟩⟩
      by_contra hne
      exact hb (target_reaches_of_not_avoidingReach hlu hne)
  have hxS : N.leaf x ∈ S := (hleaf x (mem_coe.2 hx)).2 rfl
  have hyS : ∀ y ∈ q, y ≠ x → N.leaf y ∉ S := fun y hy hyx h =>
    hyx ((hleaf y (mem_coe.2 hy)).1 h)
  rcases (hcr e ⟨⟨y₀, hy₀, hr₀⟩, l, hl, hls⟩).2 rfl with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · refine Or.inr ⟨hs, ht, ⟨fun y hy hyx hav => ?_, fun hb => ?_⟩, fun u hu => ?_⟩
    · exact hyS y hy hyx ((hfroml (mem_coe.2 hy) hav).1 (hsrc.2 hs))
    · exact ht ((htgt hb ⟨x, mem_coe.2 hx, .refl⟩).2 hxS)
    · rcases hside u hu with ⟨hb, hiff⟩ | ⟨hb, hiff⟩
      · exact ⟨fun h => absurd (hiff.2 h) ht, fun h => absurd hb h⟩
      · exact ⟨fun _ => hb, fun _ => hiff.1 (hsrc.2 hs)⟩
  · refine Or.inl ⟨hs, ht, ⟨fun hav => ?_, fun y hy hyx hb => ?_⟩, fun u hu => ?_⟩
    · exact hs (hsrc.1 ((hfroml (mem_coe.2 hx) hav).2 hxS))
    · exact hyS y hy hyx ((htgt hb ⟨y, mem_coe.2 hy, .refl⟩).1 ht)
    · rcases hside u hu with ⟨hb, hiff⟩ | ⟨hb, hiff⟩
      · exact ⟨fun _ => hb, fun _ => hiff.1 ht⟩
      · exact ⟨fun h => absurd (hsrc.1 (hiff.2 h)) hs, fun h => absurd h hb⟩

omit [Fintype X] [DecidableEq X] in
/-- An attachment of a taxon is the source of an arc for which it goes down, or the target of an arc for which it
goes up. -/
theorem attachesAt_cases [DecidableEq X] (hN : N.IsPhylogenetic) {q : Finset X} {x : X} (hx : x ∈ q) {v : V}
    (h : AttachesAt N (q : Set X) x v) :
    ∃ e, (IsDown N q x e ∧ N.graph.source e = v) ∨ (IsUp N q x e ∧ N.graph.target e = v) := by
  obtain ⟨e, S, hp, hvS, hend, -⟩ := h
  refine ⟨e, ?_⟩
  rcases isPendantCut_cases hN hx hp with ⟨-, ht, hd, -⟩ | ⟨hs, -, hu, -⟩
  · refine Or.inl ⟨hd, hend.resolve_right ?_⟩
    rintro rfl
    exact hvS ht
  · refine Or.inr ⟨hu, hend.resolve_left ?_⟩
    rintro rfl
    exact hvS hs

omit [Fintype X] [DecidableEq X] in
/-- A cut below a cut: the taxa below the lower arc are below the upper one. -/
theorem isBelow_of_reaches {g g' : E} {y : X} (h : N.graph.Reaches (N.graph.target g) (N.graph.source g'))
    (hy : N.IsBelow g' y) : N.IsBelow g y :=
  h.trans (Relation.ReflTransGen.head ⟨g', rfl, rfl⟩ hy)

omit [Fintype X] in
/-- There are at least three taxa besides any two taxa of a set of four: one other taxon. -/
theorem exists_third {q : Finset X} (hq : #q = 4) (x y : X) : ∃ z ∈ q, z ≠ x ∧ z ≠ y := by
  by_contra hcon
  push Not at hcon
  have hsub : q ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · simp [hzx]
    · simp [hcon z hz hzx]
  have := (card_le_card hsub).trans card_le_two
  omega

omit [Fintype X] in
/-- Two pendant cuts of a taxon are nested, on the vertices of the induced network. -/
theorem isPendantCut_nested (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4) {x : X} (hx : x ∈ q)
    {e₁ e₂ : E} {S₁ S₂ : Set V} (h₁ : IsPendantCut N (q : Set X) x e₁ S₁)
    (h₂ : IsPendantCut N (q : Set X) x e₂ S₂) :
    (∀ u ∈ inducedVertices N (q : Set X), u ∈ S₁ → u ∈ S₂) ∨
      ∀ u ∈ inducedVertices N (q : Set X), u ∈ S₂ → u ∈ S₁ := by
  obtain ⟨y, hy, hyx, -⟩ := exists_third hq x x
  have hbelow_trans : ∀ {g g' : E}, N.graph.Reaches (N.graph.target g) (N.graph.source g') →
      ∀ u, N.graph.Reaches (N.graph.target g') u → N.graph.Reaches (N.graph.target g) u := fun h u hu =>
    h.trans (Relation.ReflTransGen.head ⟨_, rfl, rfl⟩ hu)
  rcases isPendantCut_cases hN hx h₁ with ⟨-, -, ⟨hd₁, hn₁⟩, hf₁⟩ | ⟨-, -, ⟨hd₁, hn₁⟩, hf₁⟩ <;>
    rcases isPendantCut_cases hN hx h₂ with ⟨-, -, ⟨hd₂, hn₂⟩, hf₂⟩ | ⟨-, -, ⟨hd₂, hn₂⟩, hf₂⟩
  · -- both go down
    by_cases he : e₁ = e₂
    · subst he
      exact Or.inl fun u hu h => (hf₂ u hu).2 ((hf₁ u hu).1 h)
    rcases hd₁.reaches_or_reaches hN hd₂ he with h | h
    · exact Or.inr fun u hu hus => (hf₁ u hu).2 (hbelow_trans h u ((hf₂ u hu).1 hus))
    · exact Or.inl fun u hu hus => (hf₂ u hu).2 (hbelow_trans h u ((hf₁ u hu).1 hus))
  · -- the first down, the second up: their sides below are disjoint
    refine Or.inl fun u hu hus => (hf₂ u hu).2 fun hb => ?_
    obtain ⟨w, hw, hwr⟩ := hu.2
    have hb₁ := (hf₁ u hu).1 hus
    have hwx : w = x := by
      by_contra hne
      exact hn₁ w (mem_coe.1 hw) hne (hb₁.trans hwr)
    subst hwx
    exact hn₂ (hb.trans hwr)
  · -- the first up, the second down
    refine Or.inr fun u hu hus => (hf₁ u hu).2 fun hb => ?_
    obtain ⟨w, hw, hwr⟩ := hu.2
    have hb₂ := (hf₂ u hu).1 hus
    have hwx : w = x := by
      by_contra hne
      exact hn₂ w (mem_coe.1 hw) hne (hb₂.trans hwr)
    subst hwx
    exact hn₁ (hb.trans hwr)
  · -- both go up
    by_cases he : e₁ = e₂
    · subst he
      exact Or.inl fun u hu h => (hf₂ u hu).2 ((hf₁ u hu).1 h)
    rcases (hd₁ y hy hyx).reaches_or_reaches hN (hd₂ y hy hyx) he with h | h
    · exact Or.inl fun u hu hus => (hf₂ u hu).2 fun hb => (hf₁ u hu).1 hus (hbelow_trans h u hb)
    · exact Or.inr fun u hu hus => (hf₁ u hu).2 fun hb => (hf₂ u hu).1 hus (hbelow_trans h u hb)

omit [Fintype X] [DecidableEq X] in
/-- The arc entering a taxon is a pendant cut of it. -/
theorem exists_isPendantCut [DecidableEq X] (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4) {x : X} (hx : x ∈ q) :
    ∃ e S, IsPendantCut N (q : Set X) x e S := by
  have : Finite E := hN.finite_arcs
  have hnt : (q : Set X).Nontrivial := Finset.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨l, hl⟩ := exists_isLeastStableAncestor hN hnt.nonempty
  obtain ⟨e, he⟩ := N.graph.exists_singleton_vertex_cut (hN.leaf_indegree x)
    ((hN.leaves _).2 ⟨x, rfl⟩)
  have hc := (he e).2 rfl
  have het : N.graph.target e = N.leaf x := by
    rcases hc with ⟨hs, ht⟩ | ⟨ht, -⟩
    · exact absurd hs ((N.graph.outdegree_eq_zero_iff _).1 ((hN.leaves _).2 ⟨x, rfl⟩) e)
    · exact ht
  have hlr := hl.1.reaches_leaf hN (mem_coe.2 hx)
  have hls : N.graph.Reaches l (N.graph.source e) := by
    rcases Relation.ReflTransGen.cases_tail hlr with h | ⟨y, hy, g, hgs, hgt⟩
    · exact absurd h (hl.1.leaf_ne hN hnt x)
    · have hge : g = e := (he g).1 (Or.inr ⟨hgt, fun h => (N.graph.outdegree_eq_zero_iff _).1
        ((hN.leaves _).2 ⟨x, rfl⟩) g (by simpa using h)⟩)
      rw [← hge, hgs]
      exact hy
  refine ⟨e, {N.leaf x}, ⟨⟨x, mem_coe.2 hx, het ▸ .refl⟩, l, hl, hls⟩, fun f _ => he f, fun y _ => ?_⟩
  simp [hN.leaf_injective.eq_iff]

omit [Fintype X] in
/-- **Every taxon has an attachment**: the largest pendant cut. -/
theorem exists_attachesAt [Fintype V] (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4) {x : X} (hx : x ∈ q) :
    ∃ v, AttachesAt N (q : Set X) x v := by
  set I := inducedVertices N (q : Set X) with hI
  let A : Set ℕ := {n | ∃ e S, IsPendantCut N (q : Set X) x e S ∧ (S ∩ I).ncard = n}
  have hne : A.Nonempty := by
    obtain ⟨e, S, h⟩ := exists_isPendantCut hN hq hx
    exact ⟨_, e, S, h, rfl⟩
  have hbd : BddAbove A := ⟨Fintype.card V, by
    rintro n ⟨e, S, -, rfl⟩
    exact (Set.ncard_le_card _).trans (by simp)⟩
  obtain ⟨e, S, hp, hn⟩ := Nat.sSup_mem hne hbd
  have hmax : ∀ e' S', IsPendantCut N (q : Set X) x e' S' → (S' ∩ I).ncard ≤ (S ∩ I).ncard := by
    intro e' S' hp'
    rw [hn]
    exact le_csSup hbd ⟨e', S', hp', rfl⟩
  have hall : ∀ e' S', IsPendantCut N (q : Set X) x e' S' → ∀ u ∈ I, u ∈ S' → u ∈ S := by
    intro e' S' hp' u hu hus
    rcases isPendantCut_nested hN hq hx hp' hp with h | h
    · exact h u hu hus
    · have hsub : S ∩ I ⊆ S' ∩ I := fun w hw => ⟨h w hw.2 hw.1, hw.2⟩
      have heq : S ∩ I = S' ∩ I := Set.eq_of_subset_of_ncard_le hsub (hmax e' S' hp') (Set.toFinite _)
      have hmem : u ∈ S ∩ I := by
        rw [heq]
        exact ⟨hus, hu⟩
      exact hmem.1
  obtain ⟨heI, hcr, hleaf⟩ := hp
  have hsI := (mem_inducedArcs_iff (N := N)).1 heI
  have hcong : ∀ t ∈ I, (t ∈ S ∪ Iᶜ ↔ t ∈ S) := fun t ht =>
    ⟨fun h' => h'.elim id fun h'' => absurd ht h'', Or.inl⟩
  have hleafI : ∀ y ∈ (q : Set X), N.leaf y ∈ I := by
    intro y hy
    obtain ⟨l, hl, -⟩ := heI.2
    exact ⟨⟨l, hl, hl.1.reaches_leaf hN hy⟩, y, hy, .refl⟩
  have hpS : IsPendantCut N (q : Set X) x e (S ∪ Iᶜ) := by
    refine ⟨heI, fun f hf => ?_, fun y hy => ?_⟩
    · have hfV := (mem_inducedArcs_iff (N := N)).1 hf
      exact (crosses_congr (hcong _ hfV.1) (hcong _ hfV.2)).trans (hcr f hf)
    · exact (hcong _ (hleafI y hy)).trans (hleaf y hy)
  have hcrosses := (hcr e heI).2 rfl
  have hfin : ∀ v, v ∉ S → v ∈ I → (N.graph.source e = v ∨ N.graph.target e = v) →
      AttachesAt N (q : Set X) x v := by
    intro v hv hvI hend
    refine ⟨e, S ∪ Iᶜ, hpS, fun h => hv ((hcong v hvI).1 h), hend, fun e' S' hp' u hu _ => ?_⟩
    by_cases huI : u ∈ I
    · exact Or.inl (hall e' S' hp' u huI hu)
    · exact Or.inr huI
  rcases hcrosses with ⟨-, ht⟩ | ⟨-, hs⟩
  · exact ⟨_, hfin _ ht hsI.2 (Or.inr rfl)⟩
  · exact ⟨_, hfin _ hs hsI.1 (Or.inl rfl)⟩

/-! #### Where the lineages are -/

section Lineages

open Phylogenetics.NMSC

variable [Fintype V] [Fintype E] {θ : MetricData E} {ρ : ℝ}

/-- All the taxa that go down move up to their attachments. -/
theorem cherryMass_taxaInj_eq_placeInj (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} (h : ∀ x ∈ q, P x = N.leaf x ∨ ∃ e, IsDown N q x e ∧ N.graph.source e = P x)
    (r : QuartetTree X) : cherryMass N θ ρ (taxaInj N q) r = cherryMass N θ ρ (placeInj q P) r := by
  have key : ∀ T : Finset X, T ⊆ q → cherryMass N θ ρ (taxaInj N q) r =
      cherryMass N θ ρ (placeInj q fun x => if x ∈ T then P x else N.leaf x) r := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      rw [← placeInj_leaf]
      simp
    | @insert x T hxT ih =>
      intro hT
      have hTq : T ⊆ q := (subset_insert _ _).trans hT
      have hxq : x ∈ q := hT (mem_insert_self _ _)
      rw [ih hTq]
      have hcongr : ∀ {Q : X → V}, Q x = P x → (∀ y, y ≠ x → Q y = if y ∈ T then P y else N.leaf y) →
          placeInj q Q = placeInj q fun y => if y ∈ insert x T then P y else N.leaf y := fun {Q} h₁ h₂ =>
        placeInj_congr fun y _ => by
          by_cases hyx : y = x
          · subst hyx
            rw [h₁, ite_eq_left (mem_insert_self _ _)]
          · rw [h₂ y hyx]
            simp [hyx]
      rcases h x hxq with hP | ⟨e, ⟨hd, hn⟩, hs⟩
      · rw [← hcongr (Q := fun y => if y ∈ T then P y else N.leaf y) (by simp [hxT, hP])
          (fun _ _ => rfl)]
      · rw [← hcongr (Q := Function.update (fun y => if y ∈ T then P y else N.leaf y) x (N.graph.source e))
          (by rw [Function.update_self, hs]) (fun y hy => Function.update_of_ne hy _ _)]
        refine cherryMass_placeInj_lift hN hθ hρ hxq ?_ ?_ (fun y hy hyx hb => ?_) r
        · rw [ite_eq_right hxT]
          exact hd.isBelow hN
        · rw [ite_eq_right hxT]
          exact hd
        · change N.graph.Reaches _ (if y ∈ T then P y else N.leaf y) at hb
          split_ifs at hb with hyT
          · rcases h y hy with hPy | ⟨g, ⟨hdg, -⟩, hsg⟩
            · rw [hPy] at hb
              exact hn y hy hyx hb
            · refine hn y hy hyx (isBelow_of_reaches ?_ (hdg.isBelow hN))
              rw [hsg]
              exact hb
          · exact hn y hy hyx hb
  have h1 := key q Subset.rfl
  rw [h1]
  exact congrArg (cherryMass N θ ρ · r) (placeInj_congr fun x hx => by simp [hx])

omit [Fintype X] [Fintype V] [Fintype E] in
/-- At most one taxon goes up. -/
theorem isUp_unique (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4) {x y : X} (hx : x ∈ q) (hy : y ∈ q)
    {e g : E} (he : IsUp N q x e) (hg : IsUp N q y g) : x = y := by
  by_contra hxy
  obtain ⟨z, hz, hzx, hzy⟩ := exists_third hq x y
  have hne : e ≠ g := by
    rintro rfl
    exact hg.2 ((he.1 y hy (Ne.symm hxy)).isBelow hN)
  rcases (he.1 z hz hzx).reaches_or_reaches hN (hg.1 z hz hzy) hne with h | h
  · exact he.2 (isBelow_of_reaches h ((hg.1 x hx hxy).isBelow hN))
  · exact hg.2 (isBelow_of_reaches h ((he.1 y hy (Ne.symm hxy)).isBelow hN))

omit [Fintype X] [Fintype V] [Fintype E] in
/-- A taxon going down, under an arc for which another goes up: its attachment is at or below that arc, and all root
paths to it use that arc. -/
theorem IsDown.attach_below (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4) {x₀ x : X} (hx : x ∈ q) (hxx : x ≠ x₀)
    {e₀ e : E} (he₀ : IsUp N q x₀ e₀) (he : IsDown N q x e) :
    N.graph.Reaches (N.graph.target e₀) (N.graph.source e) ∧ ¬ N.AvoidingReach e₀ N.root (N.graph.source e) := by
  obtain ⟨z, hz, hzx, hz₀⟩ := exists_third hq x x₀
  have hz₀' : N.Dominates e₀ z := he₀.1 z hz hz₀
  have hne : e₀ ≠ e := by
    rintro rfl
    exact he.2 z hz hzx (hz₀'.isBelow hN)
  have hnot : ¬ N.graph.Reaches (N.graph.target e) (N.graph.source e₀) := fun h =>
    he.2 z hz hzx (isBelow_of_reaches h (hz₀'.isBelow hN))
  refine ⟨((he₀.1 x hx hxx).reaches_or_reaches hN he.1 hne).resolve_right hnot, fun hav => ?_⟩
  refine he₀.1 x hx hxx ((hav.tail ⟨e, Ne.symm hne, rfl, rfl⟩).trans ?_)
  by_contra hn
  exact hnot (reaches_source_of_not_avoidingReach (he.1.isBelow hN) hn)

/-- **The case of a taxon going up.** Let the taxa `q`, and their images under `π`, have the same attachments `v`, and
let a taxon `x₀` of `q` go up. Then the masses of the quartet trees agree. -/
theorem cherryMass_eq_of_isUp (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) (π : Equiv.Perm X) {v : X → V}
    (hA : ∀ x ∈ q, ∃ e, (IsDown N q x e ∧ N.graph.source e = v x) ∨ (IsUp N q x e ∧ N.graph.target e = v x))
    (hB : ∀ x ∈ q, ∃ e, (IsDown N (q.map π.toEmbedding) (π x) e ∧ N.graph.source e = v x) ∨
      (IsUp N (q.map π.toEmbedding) (π x) e ∧ N.graph.target e = v x))
    {x₀ : X} (hx₀ : x₀ ∈ q) {e₀ : E} (he₀ : IsUp N q x₀ e₀) (htv : N.graph.target e₀ = v x₀)
    {r : QuartetTree X} (hr : r ∈ treesOn q) :
    cherryMass N θ ρ (taxaInj N q) r =
      cherryMass N θ ρ (taxaInj N (q.map π.toEmbedding)) (relabelQuartet π r) := by
  set q' := q.map π.toEmbedding with hq'
  have hq'c : #q' = 4 := by rw [hq', card_map, hq]
  have hπq : ∀ {x}, x ∈ q → π x ∈ q' := fun hx => mem_map_of_mem _ hx
  have hπs : ∀ {x'}, x' ∈ q' → π.symm x' ∈ q := fun {x'} hx' => by
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hx'
    simpa using hx
  have hdown : ∀ x ∈ q, x ≠ x₀ → ∃ e, IsDown N q x e ∧ N.graph.source e = v x := by
    intro x hx hxx
    obtain ⟨e, h | h⟩ := hA x hx
    · exact ⟨e, h⟩
    · exact absurd (isUp_unique hN hq hx hx₀ h.1 he₀) hxx
  have hbel : ∀ x ∈ q, N.graph.Reaches (v x₀) (v x) := by
    intro x hx
    by_cases hxx : x = x₀
    · rw [hxx]
      exact .refl
    · obtain ⟨e, hd, hs⟩ := hdown x hx hxx
      rw [← htv, ← hs]
      exact (hd.attach_below hN hq hx hxx he₀).1
  have hdom : ∀ x ∈ q, x ≠ x₀ → ¬ N.AvoidingReach e₀ N.root (v x) := by
    intro x hx hxx
    obtain ⟨e, hd, hs⟩ := hdown x hx hxx
    rw [← hs]
    exact (hd.attach_below hN hq hx hxx he₀).2
  have hx₀b : N.leaf x₀ ∉ belowSet N e₀ := fun h => he₀.2 (mem_belowSet.1 h)
  have hdv₀ : v x₀ ∉ (belowSet N e₀).erase (N.graph.target e₀) := by
    rw [← htv]
    exact notMem_erase _ _
  -- the taxa going up in the image
  let upQ : X → Prop := fun x => ∃ e, IsUp N q' (π x) e ∧ N.graph.target e = v x
  have hup : ∀ x ∈ q, upQ x → v x = v x₀ ∧ ¬ N.IsBelow e₀ (π x) := by
    rintro x hx ⟨e', he', hte'⟩
    obtain ⟨z, hz, hzx, hzy⟩ := exists_third hq x x₀
    have hzd : N.Dominates e₀ z := he₀.1 z hz hzy
    have hve : v x = v x₀ := by
      by_cases hxx : x = x₀
      · rw [hxx]
      · have hne : π x₀ ≠ π x := fun h => hxx (π.injective h).symm
        obtain ⟨g, hg | hg⟩ := hB x₀ hx₀
        · obtain ⟨hgd, hgs⟩ := hg
          have hz' : π z ≠ π x := fun h => hzx (π.injective h)
          have hne' : e' ≠ g := by
            rintro rfl
            exact hgd.2 (π z) (hπq hz) (fun h => hzy (π.injective h)) ((he'.1 _ (hπq hz) hz').isBelow hN)
          rcases (he'.1 _ (hπq hx₀) hne).reaches_or_reaches hN hgd.1 hne' with h | h
          · rw [hte', hgs] at h
            exact eq_of_reaches_of_reaches hN.acyclic h (hbel x hx)
          · exact absurd (isBelow_of_reaches h ((he'.1 _ (hπq hz) hz').isBelow hN))
              (hgd.2 _ (hπq hz) fun h => hzy (π.injective h))
        · exact absurd (π.injective (isUp_unique hN hq'c (hπq hx₀) (hπq hx) hg.1 he')) (Ne.symm hxx)
    refine ⟨hve, ?_⟩
    have he'e₀ : e' = e₀ := by
      have hne : π z ≠ π x := fun h => hzx (π.injective h)
      refine eq_of_target_eq_of_dominates hN hzd ?_
      rw [hte', htv, hve]
    exact he'e₀ ▸ he'.2
  -- the two placements
  let P : X → V := fun x => if x = x₀ then N.leaf x₀ else v x
  let P' : X → V := fun x' => if upQ (π.symm x') then N.leaf x' else v (π.symm x')
  have hPlift : cherryMass N θ ρ (taxaInj N q) r = cherryMass N θ ρ (placeInj q P) r := by
    refine cherryMass_taxaInj_eq_placeInj hN hθ hρ (fun x hx => ?_) r
    by_cases hxx : x = x₀
    · exact Or.inl (by simp [P, hxx])
    · obtain ⟨e, hd, hs⟩ := hdown x hx hxx
      exact Or.inr ⟨e, hd, by simp [P, hxx, hs]⟩
  have hP'lift : cherryMass N θ ρ (taxaInj N q') (relabelQuartet π r) =
      cherryMass N θ ρ (placeInj q' P') (relabelQuartet π r) := by
    refine cherryMass_taxaInj_eq_placeInj hN hθ hρ (fun x' hx' => ?_) _
    by_cases hu : upQ (π.symm x')
    · exact Or.inl (by simp [P', hu])
    · obtain ⟨e, h | h⟩ := hB _ (hπs hx')
      · rw [Equiv.apply_symm_apply] at h
        exact Or.inr ⟨e, h.1, by simp [P', hu, h.2]⟩
      · rw [Equiv.apply_symm_apply] at h
        exact absurd ⟨e, by rw [Equiv.apply_symm_apply]; exact h⟩ hu
  have hrel : cherryMass N θ ρ (placeInj q P) r =
      cherryMass N θ ρ (placeInj q' (P ∘ π.symm)) (relabelQuartet π r) := by
    rw [← relabelInj_placeInj, cherryMass_relabel]
  rw [hPlift, hP'lift, hrel]
  have hP'b : ∀ x' ∈ q', upQ (π.symm x') → N.leaf x' ∉ belowSet N e₀ := fun x' hx' hu h => by
    have := (hup _ (hπs hx') hu).2
    rw [Equiv.apply_symm_apply] at this
    exact this (mem_belowSet.1 h)
  have hr' : relabelQuartet π r ∈ treesOn q' := mem_treesOn.2 (by
    rw [taxa_relabelQuartet, mem_treesOn.1 hr])
  refine cherryMass_placeInj_eq_of_below hN hθ hρ hq'c (e₀ := e₀) (fun x' hx' h => ?_) ⟨π x₀, hπq hx₀, ?_⟩ ?_ ?_ hr'
  · -- the two placements agree strictly below
    have hxq := hπs hx'
    simp only [Function.comp, P, P'] at h ⊢
    by_cases hxx : π.symm x' = x₀
    · exfalso
      rw [ite_eq_left hxx] at h
      rcases h with h | h
      · exact hx₀b (mem_of_mem_erase h)
      · by_cases hu : upQ (π.symm x')
        · rw [ite_eq_left hu] at h
          exact hP'b x' hx' hu (mem_of_mem_erase h)
        · rw [ite_eq_right hu, hxx] at h
          exact hdv₀ h
    · by_cases hu : upQ (π.symm x')
      · exfalso
        rw [ite_eq_right hxx, ite_eq_left hu] at h
        rcases h with h | h
        · rw [(hup _ hxq hu).1] at h
          exact hdv₀ h
        · exact hP'b x' hx' hu (mem_of_mem_erase h)
      · rw [ite_eq_right hxx, ite_eq_right hu]
  · -- three at or below for the first placement
    intro x' hx' hne
    have hxx : π.symm x' ≠ x₀ := fun h => hne (by rw [← h, Equiv.apply_symm_apply])
    simp only [Function.comp, P, ite_eq_right hxx]
    rw [mem_belowSet, htv]
    exact hbel _ (hπs hx')
  · -- three at or below for the second placement
    by_cases hex : ∃ y ∈ q, upQ y
    · obtain ⟨y, hy, e', he', hte'⟩ := hex
      refine ⟨π y, hπq hy, fun x' hx' hne => ?_⟩
      have hu : ¬ upQ (π.symm x') := by
        rintro ⟨g, hg, -⟩
        rw [Equiv.apply_symm_apply] at hg
        exact hne (isUp_unique hN hq'c hx' (hπq hy) hg he')
      simp only [P', ite_eq_right hu]
      rw [mem_belowSet, htv]
      exact hbel _ (hπs hx')
    · refine ⟨π x₀, hπq hx₀, fun x' hx' _ => ?_⟩
      have hu : ¬ upQ (π.symm x') := fun h => hex ⟨_, hπs hx', h⟩
      simp only [P', ite_eq_right hu]
      rw [mem_belowSet, htv]
      exact hbel _ (hπs hx')
  · -- the positions strictly below are under `e₀`
    intro x' hx' h
    simp only [Function.comp, P] at h ⊢
    by_cases hxx : π.symm x' = x₀
    · rw [ite_eq_left hxx] at h
      exact absurd (mem_of_mem_erase h) hx₀b
    · rw [ite_eq_right hxx]
      exact hdom _ (hπs hx') hxx

/-- **The masses of the quartet trees depend only on the attachments.** -/
theorem cherryMass_eq_of_attachments (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) (π : Equiv.Perm X) {v : X → V}
    (hA : ∀ x ∈ q, ∃ e, (IsDown N q x e ∧ N.graph.source e = v x) ∨ (IsUp N q x e ∧ N.graph.target e = v x))
    (hB : ∀ x ∈ q, ∃ e, (IsDown N (q.map π.toEmbedding) (π x) e ∧ N.graph.source e = v x) ∨
      (IsUp N (q.map π.toEmbedding) (π x) e ∧ N.graph.target e = v x))
    {r : QuartetTree X} (hr : r ∈ treesOn q) :
    cherryMass N θ ρ (taxaInj N q) r =
      cherryMass N θ ρ (taxaInj N (q.map π.toEmbedding)) (relabelQuartet π r) := by
  by_cases hU : ∃ x₀ ∈ q, ∃ e₀, IsUp N q x₀ e₀ ∧ N.graph.target e₀ = v x₀
  · obtain ⟨x₀, hx₀, e₀, he₀, ht⟩ := hU
    exact cherryMass_eq_of_isUp hN hθ hρ hq π hA hB hx₀ he₀ ht hr
  by_cases hU' : ∃ x₀ ∈ q, ∃ e₀, IsUp N (q.map π.toEmbedding) (π x₀) e₀ ∧ N.graph.target e₀ = v x₀
  · -- the symmetric case
    obtain ⟨x₀, hx₀, e₀, he₀, ht⟩ := hU'
    have hq'c : #(q.map π.toEmbedding) = 4 := by rw [card_map, hq]
    have hmm : (q.map π.toEmbedding).map π.symm.toEmbedding = q := by
      ext z
      simp [mem_map_equiv]
    have hsw := cherryMass_eq_of_isUp (N := N) (θ := θ) (ρ := ρ) hN hθ hρ hq'c π.symm (v := v ∘ π.symm)
      (fun x' hx' => by
        obtain ⟨x, hx, rfl⟩ := mem_map.1 hx'
        have := hB x hx
        simpa using this)
      (fun x' hx' => by
        obtain ⟨x, hx, rfl⟩ := mem_map.1 hx'
        have := hA x hx
        simpa [hmm] using this)
      (mem_map_of_mem _ hx₀) he₀ (by simpa using ht)
      (r := relabelQuartet π r)
      (mem_treesOn.2 (by
        rw [taxa_relabelQuartet, mem_treesOn.1 hr]))
    have hinv : relabelQuartet π.symm (relabelQuartet π r) = r := by
      refine Subtype.ext ?_
      change relabelFamily π.symm (relabelFamily π r.val) = r.val
      ext B
      unfold relabelFamily
      simp only [mem_image, exists_exists_and_eq_and]
      have hC : ∀ C : Finset X, (C.map π.toEmbedding).map π.symm.toEmbedding = C := fun C => by
        ext z
        simp [mem_map_equiv]
      simp only [hC]
      simp
    rw [hsw, hmm, hinv]
  · -- no taxon goes up: the lineages all move to the attachments
    push Not at hU hU'
    have h₁ : cherryMass N θ ρ (taxaInj N q) r = cherryMass N θ ρ (placeInj q v) r := by
      refine cherryMass_taxaInj_eq_placeInj hN hθ hρ (fun x hx => Or.inr ?_) r
      obtain ⟨e, h | h⟩ := hA x hx
      · exact ⟨e, h⟩
      · exact absurd h.2 (hU x hx e h.1)
    have h₂ : cherryMass N θ ρ (taxaInj N (q.map π.toEmbedding)) (relabelQuartet π r) =
        cherryMass N θ ρ (placeInj (q.map π.toEmbedding) (v ∘ π.symm)) (relabelQuartet π r) := by
      refine cherryMass_taxaInj_eq_placeInj hN hθ hρ (fun x' hx' => Or.inr ?_) _
      obtain ⟨x, hx, rfl⟩ := mem_map.1 hx'
      obtain ⟨e, h | h⟩ := hB x hx
      · exact ⟨e, h.1, by simpa using h.2⟩
      · exact absurd h.2 (hU' x hx e h.1)
    rw [h₁, h₂, ← relabelInj_placeInj, cherryMass_relabel]

/-- A permutation of the taxa extending a map injective on a finite set. -/
theorem exists_perm_extending {q : Finset X} {g : X → X} (hg : Set.InjOn g q) :
    ∃ π : Equiv.Perm X, ∀ x ∈ q, π x = g x := by
  have hbij : Function.Bijective (fun x : {x // x ∈ q} =>
      (⟨g x.val, mem_image_of_mem g x.property⟩ : {y // y ∈ q.image g})) := by
    refine ⟨fun a b h => Subtype.ext (hg a.property b.property (congrArg Subtype.val h)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨(Equiv.ofBijective _ hbij).extendSubtype, fun x hx => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ x hx]
  rfl

/-- **Remark 3.3** (`ecto:rem3_3`), condition 2 as printed, for the NMSC with independent, correlated or common
inheritance: `p_xy|zw` does not depend on the pendant chains of the induced network. The attachments are all that is
used: the hypothesis on the core arcs is not needed, since it is one network. -/
theorem pendantChainInvariant_nmscCF (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    PendantChainInvariant N (nmscCF N θ ρ) := by
  intro s s' g hinj hs' _ hatt
  obtain ⟨π, hπ⟩ := exists_perm_extending hinj
  have hs'rel : s' = relabelQuartet π s := by
    refine Subtype.ext ?_
    rw [hs']
    change _ = relabelFamily _ _
    unfold relabelFamily
    refine image_congr fun B hB => ?_
    ext z
    simp only [Finset.mem_image, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hπ x (s.subset_taxa hB hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hπ x (s.subset_taxa hB hx)).symm⟩
  have htaxa : s'.taxa = s.taxa.map π.toEmbedding := by
    rw [hs'rel, taxa_relabelQuartet]
  have hex : ∀ x, ∃ v, x ∈ s.taxa → AttachesAt N (s.taxa : Set X) x v := fun x => by
    by_cases hx : x ∈ s.taxa
    · obtain ⟨v, hv⟩ := exists_attachesAt hN s.card_taxa hx
      exact ⟨v, fun _ => hv⟩
    · exact ⟨N.root, fun h => absurd h hx⟩
  choose v hv using hex
  rw [NMSC.nmscCF_eq_cherryMass hN hθ hρ s, NMSC.nmscCF_eq_cherryMass hN hθ hρ s', hs'rel,
    NMSC.taxa_relabelQuartet]
  refine cherryMass_eq_of_attachments hN hθ hρ s.card_taxa π (v := v)
    (fun x hx => attachesAt_cases hN hx (hv x hx)) (fun x hx => ?_) (mem_treesOn.2 rfl)
  have h := (hatt x hx (v x)).1 (hv x hx)
  rw [← hπ x hx, htaxa] at h
  exact attachesAt_cases hN (mem_map_of_mem _ hx) h

/-- `pendantChainInvariant_nmscCF` at the boundary of the parameters. -/
theorem pendantChainInvariant_nmscCF_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    PendantChainInvariant N (nmscCF N θ ρ) := fun s s' g hinj hs' hc hatt =>
  nmscCF_eq_of_forall_isMetric hθ ρ s s' fun _ hθ' =>
    pendantChainInvariant_nmscCF hN hθ' hρ s s' g hinj hs' hc hatt

/-- **Remark 3.3** (`ecto:rem3_3`), condition 2 as printed, for the displayed tree model: it is the limit of common
inheritance, as all lengths grow (`tendsto_nmscCF_addLength_displayedCF`). -/
theorem pendantChainInvariant_displayedCF [Nonempty X] (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) :
    PendantChainInvariant N (displayedCF N θ) := by
  intro s s' g hinj hs' hc hatt
  refine tendsto_nhds_unique_of_eventuallyEq (tendsto_nmscCF_addLength_displayedCF hN hθ s)
    (tendsto_nmscCF_addLength_displayedCF hN hθ s') ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  have hw : N.IsWeakMetric (addLength θ L) := ⟨fun f => add_nonneg (hθ.1 f) hL, hθ.2.1, hθ.2.2⟩
  exact pendantChainInvariant_nmscCF_weak hN hw ⟨zero_le_one, le_rfl⟩ s s' g hinj hs' hc hatt

end Lineages

end Pendant

end ECToBlob
