module

public import AllmanEtAl2023.TrivialEdges
public import Basic.Defs
public import Basic.Testing.IID
public import External.Rhodes2020.Theorem2

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the outline of an algorithm, in Section 5

"Beginning with a collection of independent gene trees on `X`, the algorithm proceeds as follows:

1. Tabulate qcCFs for all sets of four taxa.
2. Apply a statistical hypothesis test to each qcCF to judge whether the T-quartet model can be rejected. If so, the taxa form a putative B-quartet on the induced 4-taxon network. If not, infer the resolved quartet tree of blobs topology.
3. Use the B-quartet Inference Rule repeatedly to determine all putative B-quartets on the full network.
4. Treating putative B-quartets as unresolved quartet trees and T-quartets as resolved, estimate the unrooted reduced tree of blobs, using the quartet intertaxon distance (Rhodes 2020) and a tree building method.

... Like NANUQ, it can be shown to provide a statistically consistent estimate of the network features it seeks to infer." (The PMC manuscript; the last sentence isn't in the arXiv version.)

The paper gives neither the test of step 2, which it says "requires the development of a novel statistical test", nor a proof of consistency. So:

* `stepTwoB`, `stepTwoT`, `stepThree`, `outline`: the four steps, for a test `reject` and a choice `top` of the topology. Step 1 is `quartetCount unroot ω`. A tree building method may return edges of length zero, and these are contracted.
* `outline_eq_of_correct`: from right answers on all sets of four taxa, the output is the tree of blobs. The proof is that of Theorem 4 (`closure_complete`, `closure_sound`), with Rhodes's Theorem 2 for the distance.
* `outline_consistent`: **the consistency of the outline for any test that is right with probability tending to one on each set of four taxa.**
* The test that the later paper developed, TINNiK's cut test, its counts of operations, and the consistency of the outline for generic parameters, from TINNiK's Theorem 4, are in `TINNiK.AllmanOutline`, outside this directory: this directory imports no later paper.
* `cutLine`, `cutLine_inter`: "the point `(1/3, 1/3, 1/3)` where the 3 model lines intersect".

The sentence after: "For edges between trivial blobs, it is straightforward to see that edge lengths are identifiable, and heuristics such as those used by ASTRAL (Sayyari and Mirarab 2016) for species tree inference provide a fast estimate of them." `astralLength` is the estimate of Sayyari and Mirarab's Theorem 2, which was read in the PMC copy, PMC4915361: `-ln (3/2 (1 - z))` for a proportion `z ≥ 1/3` of the gene trees, and `0` otherwise.

* `astralLength_semidirected`: on the concordance factor, it is the length of an internal edge between trivial blobs. "Fast" isn't a mathematical claim, and it is one formula on a count.
* `tendsto_astralLength`, `astralLength_semidirected_consistent`: on `m` independent gene trees, it converges in probability, by the weak law of large numbers.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace AllmanEtAl2023.Algorithm

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The steps -/

section Steps

variable (reject : (QuartetTree X → ℝ) → Finset X → Prop) (top : (QuartetTree X → ℝ) → Finset X → QuartetTree X)

/-- **Step 2, the putative B-quartets**: the sets of four taxa on which the T-quartet model is rejected. -/
def stepTwoB (c : QuartetTree X → ℝ) : Set (Finset X) := {q | q.card = 4 ∧ reject c q}

/-- **Step 2, the resolved topologies** of the other sets of four taxa. -/
def stepTwoT (c : QuartetTree X → ℝ) : Set (QuartetTree X) := {s | ¬ reject c s.taxa ∧ s = top c s.taxa}

/-- **Step 3**: "use the B-quartet Inference Rule repeatedly". -/
def stepThree (c : QuartetTree X → ℝ) : Set (Finset X) := {q | BInferred (stepTwoB reject c) (stepTwoT reject top c) q}

/-- **Step 4**, and the output of the outline, on the counts `c` of step 1: the tree of the distance, with a tree building method `M`. An edge the method returned with length zero is contracted. -/
def outline (M : TreeBuilder X) (c : QuartetTree X → ℝ) : Finset (Finset X) :=
  let B := stepThree reject top c
  let built := M (quartetDistance B {s | s ∈ stepTwoT reject top c ∧ s.taxa ∉ B})
  built.1.filter fun A => A ∉ internalSides built.1 ∨ 0 < built.2 A

end Steps

/-! ### From right answers on four taxa -/

section Deterministic

omit [Fintype X] in
/-- `BInferred` holds only of 4-taxon sets. -/
theorem card_of_bInferred {B₀ : Set (Finset X)} {τ : Set (QuartetTree X)}
    (hB₀ : ∀ q ∈ B₀, q.card = 4) {q : Finset X} (h : BInferred B₀ τ q) : q.card = 4 := by
  have key : ∀ {a b c d e : X} {q : Finset X}, ({a, b, c, d, e} : Finset X).card = 5 →
      q ∈ ({{a, b, c, e}, {a, b, d, e}, {a, c, d, e}} : Finset (Finset X)) → q.card = 4 := by
    intro a b c d e q h5 hq
    obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := AllmanEtAl2023.ne_of_card_five h5
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact TreeMetric.card_four_of_ne hab hac hae hbc hbe hce
    · exact TreeMetric.card_four_of_ne hab had hae hbd hbe hde
    · exact TreeMetric.card_four_of_ne hac had hae hcd hce hde
  induction h with
  | base q hq => exact hB₀ q hq
  | ruleB a b c d e t q h5 _ _ _ _ hq _ _ _ => exact key h5 hq
  | ruleT a b c d e s q h5 _ _ _ _ _ hq _ _ => exact key h5 hq

/-- The quartet distance depends only on the 4-taxon sets in its first argument. -/
theorem quartetDistance_congr {Bq Bq' : Set (Finset X)} {τ : Set (QuartetTree X)}
    (h1 : ∀ q : Finset X, q.card = 4 → (q ∈ Bq ↔ q ∈ Bq')) (x y : X) :
    quartetDistance Bq τ x y = quartetDistance Bq' τ x y := by
  unfold quartetDistance
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, ↓reduceIte]
    have : (univ.filter fun q : Finset X =>
        q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ (q ∈ Bq ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y)) =
        univ.filter fun q : Finset X =>
        q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ (q ∈ Bq' ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y) := by
      refine Finset.filter_congr fun q _ => ?_
      constructor
      · rintro ⟨h4, hx, hy, h⟩
        exact ⟨h4, hx, hy, h.imp_left (h1 q h4).mp⟩
      · rintro ⟨h4, hx, hy, h⟩
        exact ⟨h4, hx, hy, h.imp_left (h1 q h4).mpr⟩
    rw [this]

variable {V E : Type*} {N : RootedNetwork V E X}

/-- **Steps 3 and 4 are exact.** From the right answers of step 2 on all sets of four taxa, the output is the tree of blobs: step 3 gives the B-quartets (Theorem 3's combinatorial part, `closure_complete`, `closure_sound`), the distance is the tree metric of the quartet metrization of the tree of blobs (Rhodes 2020, Theorem 2), and an exact method returns it. -/
theorem outline_eq_of_correct (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {reject : (QuartetTree X → ℝ) → Finset X → Prop} {top : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    {M : TreeBuilder X} (hM : IsExactBuilder M) {c : QuartetTree X → ℝ}
    (hB : stepTwoB reject c = {q | q.card = 4 ∧ ¬ IsTreelike N q})
    (hT : stepTwoT reject top c = {s | InducedCutSplit N s}) :
    outline reject top M c = treeOfBlobs N := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hTB : IsUnrootedTree (treeOfBlobs N) := treeOfBlobs_isUnrootedTree hN
  have hBset : {q | BInferred {q' : Finset X | q'.card = 4 ∧ ¬ IsTreelike N q'}
      {s | InducedCutSplit N s} q} = {q | q.card = 4 ∧ IsBQuartet N q} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨card_of_bInferred (B₀ := {q' | q'.card = 4 ∧ ¬ IsTreelike N q'}) (fun q hq => hq.1) h,
        AllmanEtAl2023.closure_sound hN h⟩
    · rintro ⟨h4, h⟩
      exact AllmanEtAl2023.closure_complete hN h4 h
  have hτ : {s : QuartetTree X | s ∈ {s | InducedCutSplit N s} ∧
      s.taxa ∉ {q | q.card = 4 ∧ IsBQuartet N q}} = {s | Displays (treeOfBlobs N) s} := by
    ext s
    simp only [Set.mem_ofPred_eq, AllmanEtAl2023.displays_treeOfBlobs_iff hN s,
      QuartetTree.card_taxa, true_and]
  have hdist : quartetDistance {q | q.card = 4 ∧ IsBQuartet N q}
      {s | Displays (treeOfBlobs N) s} =
      treeMetric (treeOfBlobs N) (External.Rhodes2020.quartetWeight (treeOfBlobs N)) := by
    funext x y
    by_cases hxy : x = y
    · subst hxy
      simp only [quartetDistance, ↓reduceIte, treeMetric]
      refine (Finset.sum_eq_zero fun A hA => ?_).symm
      have := Finset.mem_filter.mp hA
      exact absurd this.2.1 this.2.2
    · rw [External.Rhodes2020.theorem2 hTB hxy]
      exact quartetDistance_congr (fun q h4 => by
        simp only [Set.mem_ofPred_eq, h4, true_and]; rfl) x y
  have hw : ∀ A ∈ treeOfBlobs N, 0 < External.Rhodes2020.quartetWeight (treeOfBlobs N) A ∧
      External.Rhodes2020.quartetWeight (treeOfBlobs N) Aᶜ =
        External.Rhodes2020.quartetWeight (treeOfBlobs N) A := fun A hA =>
    ⟨lt_of_lt_of_le two_pos (External.Rhodes2020.quartetWeight_ge_two hTB hX hA),
      External.Rhodes2020.quartetWeight_compl _ _⟩
  obtain ⟨h0, h1, h2, h3⟩ := hM _ _ hTB hw
  have hS : stepThree reject top c = {q | q.card = 4 ∧ IsBQuartet N q} := by
    unfold stepThree
    rw [hB, hT, hBset]
  simp only [outline]
  rw [hS, hT, hτ, hdist]
  have hX2 : 2 ≤ Fintype.card X := by omega
  have hTfam := (isUnrootedTree_iff hX2 _).mp hTB
  have hbuilt := (isUnrootedTree_iff hX2 _).mp h0
  ext A
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hA, hor⟩
    by_contra hnA
    rcases hor with hor | hpos
    · -- a side of a tree that is not internal is a singleton or the complement of one
      apply hnA
      have hne := hbuilt.nonempty A hA
      have hne' := hbuilt.compl_nonempty A hA
      simp only [internalSides, Finset.mem_filter, not_and_or, not_le] at hor
      rcases hor with hor | hor | hor
      · exact absurd hA hor
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp
          (le_antisymm (by omega) (Finset.card_pos.mpr hne))
        exact hTfam.singleton_mem x
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
          (le_antisymm (by omega) (Finset.card_pos.mpr hne'))
        have := hTfam.compl_mem _ (hTfam.singleton_mem x)
        rwa [← hx, compl_compl] at this
    · exact absurd hpos (not_lt.mpr (h3 A hA hnA))
  · intro hA
    refine ⟨h1 hA, Or.inr ?_⟩
    rw [h2 A hA]
    exact lt_of_lt_of_le two_pos (External.Rhodes2020.quartetWeight_ge_two hTB hX hA)

/-- The right answers on a set of four taxa: the T-quartet model is rejected without a cut-edge split on the induced network, and with one it isn't, and the topology inferred is that split. -/
def RightOn (N : RootedNetwork V E X) (reject : (QuartetTree X → ℝ) → Finset X → Prop) (top : (QuartetTree X → ℝ) → Finset X → QuartetTree X)
    (c : QuartetTree X → ℝ) (q : Finset X) : Prop :=
  (¬ IsTreelike N q → reject c q) ∧ ∀ s ∈ treesOn q, InducedCutSplit N s → ¬ reject c q ∧ top c q = s

omit [Fintype X] in
/-- The right answers on each set of four taxa are the right sets of step 2. -/
theorem steps_of_rightOn [Fintype X] {reject : (QuartetTree X → ℝ) → Finset X → Prop} {top : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {c : QuartetTree X → ℝ}
    (h : ∀ q : Finset X, q.card = 4 → RightOn N reject top c q) :
    stepTwoB reject c = {q | q.card = 4 ∧ ¬ IsTreelike N q} ∧ stepTwoT reject top c = {s | InducedCutSplit N s} := by
  constructor
  · ext q
    simp only [stepTwoB, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h4, hr⟩
      refine ⟨h4, ?_⟩
      rintro ⟨s, hs, hcs⟩
      exact ((h q h4).2 s hs hcs).1 hr
    · rintro ⟨h4, hnt⟩
      exact ⟨h4, (h q h4).1 hnt⟩
  · ext s
    simp only [stepTwoT, Set.mem_ofPred_eq]
    have hs4 := QuartetTree.card_taxa s
    have hsmem : s ∈ treesOn s.taxa := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    constructor
    · rintro ⟨hr, hst⟩
      have htl : IsTreelike N s.taxa := by
        by_contra hnt
        exact hr ((h _ hs4).1 hnt)
      obtain ⟨s₀, hs₀, hc₀⟩ := htl
      have h1 := ((h _ hs4).2 s₀ hs₀ hc₀).2
      rw [hst, h1]
      exact hc₀
    · intro hc
      obtain ⟨h1, h2⟩ := (h _ hs4).2 s hsmem hc
      exact ⟨h1, h2.symm⟩

end Deterministic

/-! ### Consistency -/

section Consistency

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

/-- **The consistency of the outline, for a test that is right on each set of four taxa with probability tending to one** (`a:claim:outline-consistent`). `m` independent gene trees from the NMSC, the test at sample size `m`: the outline returns the tree of blobs with probability tending to one. -/
theorem outline_consistent (hN : N.IsPhylogenetic) (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    {reject : ℕ → (QuartetTree X → ℝ) → Finset X → Prop} {top : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hright : ∀ q : Finset X, q.card = 4 → Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      RightOn N (reject m) top (quartetCount unroot ω) q) atTop (𝓝 1))
    {M : TreeBuilder X} (hM : IsExactBuilder M) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      outline (reject m) top M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd : IsDist (geneTreeDist N θ 0) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hall := tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
    (fun q m ω => RightOn N (reject m) top (quartetCount unroot ω) q.val) (fun q => hright q.val q.property)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) hall
  obtain ⟨hB, hT⟩ := steps_of_rightOn (N := N) (reject := reject m) (top := top) (c := quartetCount unroot ω) fun q hq => hω ⟨q, hq⟩
  exact outline_eq_of_correct hN hX hM hB hT

end Consistency

/-! ### The three lines -/

section Lines

/-- The line of `CF`s of the first topology, in `(CF_{ab|cd}, CF_{ac|bd}, CF_{ad|bc})`. The others are its images. -/
def cutLine : Fin 3 → ℝ → ℝ × ℝ × ℝ
  | 0, v => (v, (1 - v) / 2, (1 - v) / 2)
  | 1, v => ((1 - v) / 2, v, (1 - v) / 2)
  | 2, v => ((1 - v) / 2, (1 - v) / 2, v)

/-- **"The point `(1/3, 1/3, 1/3)` where the 3 model lines intersect"**: it is on all three, and two of them meet nowhere else. -/
theorem cutLine_inter : (∀ i, cutLine i (1 / 3) = (1 / 3, 1 / 3, 1 / 3)) ∧
    ∀ i j, i ≠ j → ∀ v w, cutLine i v = cutLine j w → cutLine i v = (1 / 3, 1 / 3, 1 / 3) := by
  constructor
  · intro i
    fin_cases i <;> simp only [cutLine, Prod.mk.injEq] <;> norm_num
  · intro i j hij v w h
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (simp only [cutLine, Prod.mk.injEq] at h ⊢
         obtain ⟨h1, h2, h3⟩ := h
         refine ⟨?_, ?_, ?_⟩ <;> linarith)

end Lines

/-! ### The estimate of the lengths of edges -/

section Lengths

/-- **The estimate of Sayyari and Mirarab**, Theorem 2: the length of a branch from the proportion `z` of the gene trees with its quartet, `-ln (3/2 (1 - z))` for `z ≥ 1/3`, and 0 otherwise. -/
def astralLength (z : ℝ) : ℝ := if 1 / 3 ≤ z then -Real.log (3 / 2 * (1 - z)) else 0

theorem astralLength_eq_max {z : ℝ} (hz : z < 1) : astralLength z = max 0 (-Real.log (3 / 2 * (1 - z))) := by
  unfold astralLength
  have hpos : 0 < 3 / 2 * (1 - z) := by linarith
  split_ifs with h
  · refine (max_eq_right ?_).symm
    have : Real.log (3 / 2 * (1 - z)) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
    linarith
  · refine (max_eq_left ?_).symm
    have : 0 ≤ Real.log (3 / 2 * (1 - z)) := Real.log_nonneg (by linarith)
    linarith

/-- The estimate is continuous below 1. -/
theorem continuousAt_astralLength {z : ℝ} (hz : z < 1) : ContinuousAt astralLength z := by
  have hc : ContinuousAt (fun z : ℝ => max 0 (-Real.log (3 / 2 * (1 - z)))) z := by
    refine continuousAt_const.max (ContinuousAt.neg (ContinuousAt.log (by fun_prop) ?_))
    have : 0 < 3 / 2 * (1 - z) := by linarith
    exact this.ne'
  refine hc.congr ?_
  filter_upwards [gt_mem_nhds hz] with y hy
  exact (astralLength_eq_max hy).symm

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

/-- **The estimate on the concordance factor**, from the formula of the length: if the length is nonnegative, and the formula holds, the estimate is the length. -/
theorem astralLength_of_eq {t F : ℝ} (ht : 0 ≤ t) (h : t = -Real.log (3 / 2 * (1 - F))) : astralLength F = t := by
  unfold astralLength
  rw [ite_eq_left, h]
  by_contra hF
  have h1 : 1 < 3 / 2 * (1 - F) := by
    have : F < 1 / 3 := not_le.1 hF
    linarith
  have := Real.log_pos h1
  linarith

/-- **"For edges between trivial blobs ... heuristics such as those used by ASTRAL ... provide a fast estimate of them"** (`a:claim:astral-length`, Section 5): on the exact concordance factor, the estimate of Sayyari and Mirarab is the length of an internal edge between trivial blobs of `𝒩⁻`. -/
theorem astralLength_semidirected (hN : IsBinaryNetwork N) (hX : Nontrivial X) (e : SemiE hN hX)
    (hs : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.source e)))
    (ht : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.target e)))
    (hls : ∀ x, (semidirected hN hX).leaf x ≠ (semidirected hN hX).graph.source e)
    (hlt : ∀ x, (semidirected hN hX).leaf x ≠ (semidirected hN hX).graph.target e) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ∀ θ : MetricData E, N.IsMetric θ →
      astralLength (nmscCF N θ 0 (quartetTree a b c d h)) = (semidirectedMetric hN hX θ).length e := by
  obtain ⟨a, b, c, d, h, hF⟩ := TrivialEdges.semidirected_length_eq hN hX e hs ht hls hlt
  refine ⟨a, b, c, d, h, fun θ hθ => astralLength_of_eq ?_ (hF θ hθ)⟩
  have hw := hθ.isWeakMetric.1
  unfold semidirectedMetric
  simp only
  split_ifs
  · exact add_nonneg (hw _) (hw _)
  · exact hw _

/-- **The proportion of `m` independent gene trees that display a quartet tree converges to its concordance factor.** -/
theorem tendsto_proportion [Nonempty X] (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) (s : QuartetTree X) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω => |quartetCount unroot ω s / m - nmscCF N θ 0 s| < ε) atTop (𝓝 1) := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd : IsDist (geneTreeDist N θ 0) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  refine (iidProb_weak_law hd (fun g => if Displays (unroot g) s then (1 : ℝ) else 0) hε).congr fun m => ?_
  congr 1
  funext ω
  have h1 : ∑ i, (if Displays (unroot (ω i)) s then (1 : ℝ) else 0) = quartetCount unroot ω s := by
    unfold quartetCount
    rw [Finset.card_filter]
    push_cast
    rfl
  have h2 : ∑ g, geneTreeDist N θ 0 g * (if Displays (unroot g) s then (1 : ℝ) else 0) = nmscCF N θ 0 s := by
    unfold nmscCF
    refine sum_congr rfl fun g _ => ?_
    split_ifs <;> simp
  rw [h1, h2]

/-- **The estimate on `m` independent gene trees converges in probability** to its value on the concordance factor, which is below 1. -/
theorem tendsto_astralLength (hN : N.IsPhylogenetic) (hc : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
      |astralLength (quartetCount unroot ω (quartetTree a b c d h) / m) - astralLength (nmscCF N θ 0 (quartetTree a b c d h))| < ε) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd : IsDist (geneTreeDist N θ 0) := ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩
  have hF : nmscCF N θ 0 (quartetTree a b c d h) < 1 := by
    have h1 := NetworkNk.sum_cfTriple_weak hN hθ.isNormalized h
    have h2 := nmscCF_pos hN hθ hρ (quartetTree a c b d (card_acbd h))
    have h3 := nmscCF_pos hN hθ hρ (quartetTree a d b c (card_adbc h))
    linarith
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 (continuousAt_astralLength hF) ε hε
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) (tendsto_proportion hN hθ (quartetTree a b c d h) hδ)
  have := hcont (x := quartetCount unroot ω (quartetTree a b c d h) / m) (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at this

/-- **The estimate of the length of an internal edge between trivial blobs is consistent.** -/
theorem astralLength_semidirected_consistent (hN : IsBinaryNetwork N) (hX : Nontrivial X) (hc : 4 ≤ Fintype.card X) (e : SemiE hN hX)
    (hs : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.source e)))
    (ht : IsTrivialBlob (semidirected hN hX).graph (blobOf (semidirected hN hX).graph ((semidirected hN hX).graph.target e)))
    (hls : ∀ x, (semidirected hN hX).leaf x ≠ (semidirected hN hX).graph.source e)
    (hlt : ∀ x, (semidirected hN hX).leaf x ≠ (semidirected hN hX).graph.target e) :
    ∃ (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4), ∀ θ : MetricData E, N.IsMetric θ → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
        |astralLength (quartetCount unroot ω (quartetTree a b c d h) / m) - (semidirectedMetric hN hX θ).length e| < ε) atTop (𝓝 1) := by
  obtain ⟨a, b, c, d, h, hF⟩ := astralLength_semidirected hN hX e hs ht hls hlt
  refine ⟨a, b, c, d, h, fun θ hθ ε hε => ?_⟩
  have := tendsto_astralLength hN.isPhylogenetic hc hθ h hε
  rwa [hF θ hθ] at this

end Lengths

end AllmanEtAl2023.Algorithm
