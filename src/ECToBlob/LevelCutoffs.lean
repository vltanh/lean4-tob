module

public import ECToBlob.InPassing

/-!
# ECToBlob, lines 1164-1167: the `o(n)` cutoffs of `α_n`

"Any valid choice needs `α_n, β_n → 0` in order to fail to reject a true null hypothesis consistently. However, we also need `o(n)` cutoff
values (e.g., `log(n)` in the proof), to ensure they grow slower than the non-centrality parameter of each non-null hypothesis, so that a
false null hypothesis is rejected with increasing probability."

For `β_n` this is `BinaryLaw.OnFour.tendsto_log_beta_of_consistent`. This file is the same for `α_n`, at a law near the T1 null.

* `OnBlob.net`: a binary network on four taxa whose only non-trivial blob is a 4-blob, a 4-sunlet. Its tree of blobs is the star
  (`treeOfBlobs_eq`), and `BinaryLaw.OnFour.T₀`, with the edge `01|23`, resolves it, with a false edge.
* `OnBlob.law q`: the law `(1/2, 1/4 + q, 1/4 - q)` on the three binary gene trees. It meets both directions of Assumption 1
  (`law_assumption1`). As `q → 0` it tends to the T1 null of `01|23`, a false null with a small non-centrality parameter, while the star test
  still rejects.
* `OnBlob.tendsto_log_alpha_of_consistent`: if `log β_n / n → 0` and the output is the tree of blobs with probability tending to one on all
  these laws, then `log α_n / n → 0`. Otherwise, at a small `q`, the T1 test doesn't reject, and the false edge stays.
* `tendsto_log_levels_of_valid`: levels valid for all the laws of Theorem 8.2 have `o(n)` cutoffs. The cutoff of `α_n` is `-log α_n` up to the
  factor `2` of the `χ²₁` tail: `Phylogenetics.QuartetTests.chiSqOneTail_log_isEquivalent`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob.BinaryLaw

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.FalseEdge ECToBlob.Framework
open ECToBlob.DisplayedTree ECToBlob.FinNetwork

/-- If all the overall p-values of the sequence reach the level, both rules select the tree after Step 3. -/
theorem ectoblob_eq_afterStar_of_forall_le {X : Type*} [Fintype X] [DecidableEq X] {o : ECToBlobOptions} {α β : ℝ}
    {c : QuartetTree X → ℝ} {T₀ : Finset (Finset X)} (h : ∀ i, α ≤ treeT1P o c (treeSeq o β c T₀ i)) :
    ectoblob o α β c T₀ = afterStar o β c T₀ := by
  have hsel : selectedIteration o α β c T₀ = 0 := by
    unfold selectedIteration
    cases o.rule with
    | early => exact Nat.sInf_eq_zero.2 (Or.inl ⟨Nat.zero_le _, h 0⟩)
    | late =>
      refine ite_eq_right ?_
      rintro ⟨i, -, hi⟩
      exact absurd hi (not_lt_of_ge (h i))
  unfold ectoblob
  rw [hsel]
  rfl

namespace OnBlob

/-- The tails of the arcs of a 4-sunlet: the taxa `a, b, c, d = 0, 1, 2, 3`, the reticulation `h = 4`, with its parents `u = 5` and `w = 6`, the
vertex `v = 7` and the root `r = 8`, on the cycle. The arcs are, in order, `r u`, `r v`, `v w`, `v c`, `u h`, `u b`, `w h`, `w d`, `h a`. -/
def src : Fin 9 → Fin 9 := ![8, 8, 7, 7, 5, 5, 6, 6, 4]

/-- The heads of the arcs. -/
def tgt : Fin 9 → Fin 9 := ![5, 7, 6, 2, 4, 1, 4, 3, 0]

/-- The taxa, as vertices. -/
def lf : Fin 4 → Fin 9 := ![0, 1, 2, 3]

/-- What each vertex reaches. -/
def desc : Fin 9 → Finset (Fin 9) :=
  ![{0}, {1}, {2}, {3}, {0, 4}, {0, 1, 4, 5}, {0, 3, 4, 6}, {0, 2, 3, 4, 6, 7}, {0, 1, 2, 3, 4, 5, 6, 7, 8}]

/-- What the root reaches off each arc. -/
def avoid : Fin 9 → Finset (Fin 9) :=
  ![{0, 2, 3, 4, 6, 7, 8}, {0, 1, 4, 5, 8}, {0, 1, 2, 4, 5, 7, 8}, {0, 1, 3, 4, 5, 6, 7, 8}, {0, 1, 2, 3, 4, 5, 6, 7, 8},
    {0, 2, 3, 4, 5, 6, 7, 8}, {0, 1, 2, 3, 4, 5, 6, 7, 8}, {0, 1, 2, 4, 5, 6, 7, 8}, {1, 2, 3, 4, 5, 6, 7, 8}]

theorem tables : Tables src tgt 8 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The 4-sunlet**, as a network. -/
abbrev net : RootedNetwork (Fin 9) (Fin 9) (Fin 4) := FinNetwork.net src tgt 8 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem net_isBinary : net.IsBinary := by
  have hin : ∀ v : Fin 9, net.graph.indegree v = (univ.filter fun e => tgt e = v).card := by
    intro v
    rw [DirectedMultigraph.indegree, Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    simp [FinNetwork.net]
  have hout : ∀ v : Fin 9, net.graph.outdegree v = (univ.filter fun e => src e = v).card := by
    intro v
    rw [DirectedMultigraph.outdegree, Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    simp [FinNetwork.net]
  refine ⟨?_, fun v hv ho => ?_⟩
  · rw [hout]
    decide
  · rw [hout] at ho
    rw [hin, hout]
    revert v
    decide

/-- No set of four taxa has a trivial 4-blob: the 4-blob is not a multifurcation. -/
theorem not_hasTrivialFourBlob {Q : Finset (Fin 4)} (hQ : Q.card = 4) : ¬ HasTrivialFourBlob net Q := by
  have : ∀ Q : Finset (Fin 4), Q.card = 4 → ∀ v, ¬ HubT src tgt lf desc avoid Q v := by decide
  rw [tables.hasTrivialFourBlob_iff net_isPhylogenetic hQ]
  rintro ⟨v, hv⟩
  exact this Q hQ v hv

/-- No quartet tree is a cut split: `01|23`, `02|13` and `03|12` are all split by the 4-blob. -/
theorem not_inducedCutSplit (s : QuartetTree (Fin 4)) : ¬ InducedCutSplit net s := by
  intro h
  obtain ⟨a, b, c, d, hc, -, hr⟩ := exists_rdom_of_inducedCutSplit net_isPhylogenetic h
  have hdec : ∀ a b c d : Fin 4, ({a, b, c, d} : Finset (Fin 4)).card = 4 → ¬ RDomT tgt lf desc avoid a b c d := by decide
  exact hdec a b c d hc (tables.rdom_iff.1 hr)

/-- **The tree of blobs is the star.** -/
theorem treeOfBlobs_eq : treeOfBlobs net = unroot {univ, {0}, {1}, {2}, {3}} := by
  ext A
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  unfold unroot
  revert A
  decide

theorem isResolutionOf_T₀ : IsResolutionOf OnFour.T₀ (treeOfBlobs net) := by
  refine ⟨OnFour.T₀_isUnrootedTree, ?_⟩
  rw [treeOfBlobs_eq]
  unfold OnFour.T₀ OnFour.hier unroot
  decide

/-- `T₀` has an edge that isn't in the tree of blobs: the output `T₀` is wrong. -/
theorem T₀_ne : OnFour.T₀ ≠ treeOfBlobs net := by
  rw [treeOfBlobs_eq]
  unfold OnFour.T₀ OnFour.hier unroot
  decide

/-- The class of a quartet tree on four taxa: the taxon with `0` in its cherry, less one. -/
def cls (s : QuartetTree (Fin 4)) : Fin 3 :=
  if ({0, 1} : Finset (Fin 4)) ∈ s.val then 0 else if ({0, 2} : Finset (Fin 4)) ∈ s.val then 1 else 2

/-- The weights of the law. -/
def wt (q : ℝ) : Fin 3 → ℝ := ![1 / 2, 1 / 4 + q, 1 / 4 - q]

/-- **The law `(1/2, 1/4 + q, 1/4 - q)`** on the three binary trees on four taxa. -/
def law (q : ℝ) : BinaryGeneTree (Fin 4) → ℝ := pointLaw OnFour.gene (wt q)

theorem law_isDist {q : ℝ} (h0 : 0 < q) (h1 : q < 1 / 4) : IsDist (law q) := by
  refine pointLaw_isDist (fun i => ?_) ?_
  · fin_cases i
    · show (0 : ℝ) ≤ 1 / 2
      norm_num
    · show (0 : ℝ) ≤ 1 / 4 + q
      linarith
    · show (0 : ℝ) ≤ 1 / 4 - q
      linarith
  · rw [Fin.sum_univ_three]
    show 1 / 2 + (1 / 4 + q) + (1 / 4 - q) = 1
    ring

theorem dsp_cases : ∀ B ∈ powersetCard 2 (univ : Finset (Fin 4)), ∀ C ∈ powersetCard 2 (univ : Finset (Fin 4)), Disjoint B C →
    ((B = {0, 1} ∨ C = {0, 1}) ∧ OnFour.dsp 0 B C ∧ ¬ OnFour.dsp 1 B C ∧ ¬ OnFour.dsp 2 B C) ∨
    (¬ (B = {0, 1} ∨ C = {0, 1}) ∧ (B = {0, 2} ∨ C = {0, 2}) ∧ ¬ OnFour.dsp 0 B C ∧ OnFour.dsp 1 B C ∧ ¬ OnFour.dsp 2 B C) ∨
    (¬ (B = {0, 1} ∨ C = {0, 1}) ∧ ¬ (B = {0, 2} ∨ C = {0, 2}) ∧ (B = {0, 3} ∨ C = {0, 3}) ∧ ¬ OnFour.dsp 0 B C ∧
      ¬ OnFour.dsp 1 B C ∧ OnFour.dsp 2 B C) := by
  decide

/-- What a quartet tree on four taxa is. -/
theorem cases_val (s : QuartetTree (Fin 4)) :
    (∃ B C, s.val = {B, C} ∧ s.taxa = B ∪ C ∧ (B = {0, 1} ∨ C = {0, 1}) ∧ OnFour.dsp 0 B C ∧ ¬ OnFour.dsp 1 B C ∧ ¬ OnFour.dsp 2 B C) ∨
    (∃ B C, s.val = {B, C} ∧ s.taxa = B ∪ C ∧ ¬ (B = {0, 1} ∨ C = {0, 1}) ∧ (B = {0, 2} ∨ C = {0, 2}) ∧ ¬ OnFour.dsp 0 B C ∧
      OnFour.dsp 1 B C ∧ ¬ OnFour.dsp 2 B C) ∨
    (∃ B C, s.val = {B, C} ∧ s.taxa = B ∪ C ∧ ¬ (B = {0, 1} ∨ C = {0, 1}) ∧ ¬ (B = {0, 2} ∨ C = {0, 2}) ∧ (B = {0, 3} ∨ C = {0, 3}) ∧
      ¬ OnFour.dsp 0 B C ∧ ¬ OnFour.dsp 1 B C ∧ OnFour.dsp 2 B C) := by
  obtain ⟨B, C, hs, hB, hC, hd, ht⟩ := s.exists_eq_pair
  rcases dsp_cases B (mem_powersetCard.2 ⟨subset_univ _, hB⟩) C (mem_powersetCard.2 ⟨subset_univ _, hC⟩) hd with h | h | h
  · exact Or.inl ⟨B, C, hs, ht, h⟩
  · exact Or.inr (Or.inl ⟨B, C, hs, ht, h⟩)
  · exact Or.inr (Or.inr ⟨B, C, hs, ht, h⟩)

theorem mem_val_iff {s : QuartetTree (Fin 4)} {B C D : Finset (Fin 4)} (hs : s.val = {B, C}) : D ∈ s.val ↔ B = D ∨ C = D := by
  rw [hs]
  simp only [mem_insert, mem_singleton]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

/-- **The concordance factors of the law.** -/
theorem displayCF_law (q : ℝ) (s : QuartetTree (Fin 4)) : displayCF (law q) Subtype.val s = wt q (cls s) := by
  unfold law
  rw [displayCF_pointLaw, Fin.sum_univ_three]
  rcases cases_val s with ⟨B, C, hs, ht, hm, h₀, h₁, h₂⟩ | ⟨B, C, hs, ht, hm, hm', h₀, h₁, h₂⟩ | ⟨B, C, hs, ht, hm, hm', -, h₀, h₁, h₂⟩
  · have hdisp : ∀ i, Displays (OnFour.gene i).1 s ↔ OnFour.dsp i B C := fun i => displays_iff_of_val hs ht
    have hc : cls s = 0 := by
      unfold cls
      rw [ite_eq_left ((mem_val_iff hs).2 (hm.imp Eq.symm Eq.symm |>.imp Eq.symm Eq.symm))]
    simp [hdisp, h₀, h₁, h₂, hc]
  · have hdisp : ∀ i, Displays (OnFour.gene i).1 s ↔ OnFour.dsp i B C := fun i => displays_iff_of_val hs ht
    have hc : cls s = 1 := by
      unfold cls
      rw [ite_eq_right fun h => hm ((mem_val_iff hs).1 h), ite_eq_left ((mem_val_iff hs).2 hm')]
    simp [hdisp, h₀, h₁, h₂, hc]
  · have hdisp : ∀ i, Displays (OnFour.gene i).1 s ↔ OnFour.dsp i B C := fun i => displays_iff_of_val hs ht
    have hc : cls s = 2 := by
      unfold cls
      rw [ite_eq_right fun h => hm ((mem_val_iff hs).1 h), ite_eq_right fun h => hm' ((mem_val_iff hs).1 h)]
    simp [hdisp, h₀, h₁, h₂, hc]

/-- Two quartet trees on four taxa of the same class are equal. -/
theorem eq_of_cls_eq {r s : QuartetTree (Fin 4)} (h : cls r = cls s) : r = s := by
  have hta : r.taxa = s.taxa := by rw [OnFour.taxa_eq_univ, OnFour.taxa_eq_univ]
  have hcase : ∀ t : QuartetTree (Fin 4), (cls t = 0 ∧ ({0, 1} : Finset (Fin 4)) ∈ t.val) ∨ (cls t = 1 ∧ ({0, 2} : Finset (Fin 4)) ∈ t.val) ∨
      (cls t = 2 ∧ ({0, 3} : Finset (Fin 4)) ∈ t.val) := by
    intro t
    rcases cases_val t with ⟨B, C, hs, -, hm, -⟩ | ⟨B, C, hs, -, hm, hm', -⟩ | ⟨B, C, hs, -, hm, hm', hm'', -⟩
    · have h₁ := (mem_val_iff hs).2 hm
      exact Or.inl ⟨by unfold cls; rw [ite_eq_left h₁], h₁⟩
    · have h₁ := (mem_val_iff hs).2 hm'
      exact Or.inr (Or.inl ⟨by unfold cls; rw [ite_eq_right fun h => hm ((mem_val_iff hs).1 h), ite_eq_left h₁], h₁⟩)
    · have h₁ := (mem_val_iff hs).2 hm''
      exact Or.inr (Or.inr ⟨by unfold cls; rw [ite_eq_right fun h => hm ((mem_val_iff hs).1 h),
        ite_eq_right fun h => hm' ((mem_val_iff hs).1 h)], h₁⟩)
  rcases hcase r with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hcase s with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · exact QuartetTree.eq_of_taxa_eq_of_mem hta h₂ h₄
  · rw [h₁, h₃] at h; exact absurd h (by decide)
  · rw [h₁, h₃] at h; exact absurd h (by decide)
  · rw [h₁, h₃] at h; exact absurd h (by decide)
  · exact QuartetTree.eq_of_taxa_eq_of_mem hta h₂ h₄
  · rw [h₁, h₃] at h; exact absurd h (by decide)
  · rw [h₁, h₃] at h; exact absurd h (by decide)
  · rw [h₁, h₃] at h; exact absurd h (by decide)
  · exact QuartetTree.eq_of_taxa_eq_of_mem hta h₂ h₄

theorem wt_injective {q : ℝ} (h0 : 0 < q) (h1 : q < 1 / 4) : Function.Injective (wt q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [wt] at hij; linarith)

/-- **Both directions of Assumption 1 hold for the law**, which isn't on the T1 null of any quartet tree and isn't uniform. -/
theorem law_assumption1 {q : ℝ} (h0 : 0 < q) (h1 : q < 1 / 4) :
    Assumption1Forward net (displayCF (law q) Subtype.val) ∧ Assumption1Converse net (displayCF (law q) Subtype.val) := by
  refine ⟨⟨fun Q hQ htr => absurd htr (not_hasTrivialFourBlob hQ), fun s hs => absurd hs (not_inducedCutSplit s)⟩,
    fun Q hQ _ hu => ?_, fun s _ hstrict => ?_⟩
  · -- not uniform
    have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
    have hQu : Q = univ := Finset.eq_univ_of_card Q (by rw [hQ]; rfl)
    have hmem : quartetTree 0 1 2 3 hc ∈ treesOn Q := by
      rw [hQu]
      exact mem_treesOn.2 (OnFour.taxa_eq_univ _)
    have hv := hu _ hmem
    rw [displayCF_law] at hv
    have hcl : cls (quartetTree 0 1 2 3 hc) = 0 := by
      unfold cls
      rw [ite_eq_left (by simp [quartetTree])]
    rw [hcl] at hv
    simp only [wt] at hv
    norm_num at hv
  · -- two alternatives have different values
    obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1 (by rw [s.card_alternatives]; norm_num : 1 < s.alternatives.card)
    have heq := hstrict.2 r hr r' hr'
    rw [displayCF_law, displayCF_law] at heq
    exact hne (eq_of_cls_eq (wt_injective h0 h1 heq))

/-- The quartet tree of the edge of `T₀`. -/
def s₀ : QuartetTree (Fin 4) := quartetTree 0 1 2 3 (by decide)

/-- The quartet tree `02|13`. -/
def r₁ : QuartetTree (Fin 4) := quartetTree 0 2 1 3 (by decide)

/-- The quartet tree `03|12`. -/
def r₂ : QuartetTree (Fin 4) := quartetTree 0 3 1 2 (by decide)

theorem cls_s₀ : cls s₀ = 0 := by
  unfold cls
  rw [ite_eq_left (by simp [s₀, quartetTree])]

theorem cls_r₁ : cls r₁ = 1 := by
  unfold cls
  rw [ite_eq_right (by unfold r₁; simp only [quartetTree_val]; decide), ite_eq_left (by simp [r₁, quartetTree])]

theorem cls_r₂ : cls r₂ = 2 := by
  unfold cls
  rw [ite_eq_right (by unfold r₂; simp only [quartetTree_val]; decide), ite_eq_right (by unfold r₂; simp only [quartetTree_val]; decide)]

theorem alternatives_s₀ : s₀.alternatives = {r₁, r₂} := by
  ext r
  rw [QuartetTree.mem_alternatives]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨-, hne⟩
    have hcl : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hcl (cls r) with h | h | h
    · exact (hne (eq_of_cls_eq (h.trans cls_s₀.symm))).elim
    · exact Or.inl (eq_of_cls_eq (h.trans cls_r₁.symm))
    · exact Or.inr (eq_of_cls_eq (h.trans cls_r₂.symm))
  · have hta : ∀ t : QuartetTree (Fin 4), t.taxa = s₀.taxa := fun t => by rw [OnFour.taxa_eq_univ, OnFour.taxa_eq_univ]
    rintro (rfl | rfl)
    · refine ⟨hta _, fun h => ?_⟩
      have := congrArg cls h
      rw [cls_r₁, cls_s₀] at this
      exact absurd this (by decide)
    · refine ⟨hta _, fun h => ?_⟩
      have := congrArg cls h
      rw [cls_r₂, cls_s₀] at this
      exact absurd this (by decide)

theorem r₁_ne_r₂ : r₁ ≠ r₂ := fun h => by
  have := congrArg cls h
  rw [cls_r₁, cls_r₂] at this
  exact absurd this (by decide)

/-- The line statistic of the law, at `01|23`. -/
theorem lineStat_wt (q : ℝ) : lineStat (fun s => wt q (cls s)) s₀ =
    2 * ((1 / 4 + q) * Real.log (1 / 4 + q) + (1 / 4 - q) * Real.log (1 / 4 - q) -
      ((1 / 4 + q) + (1 / 4 - q)) * Real.log ((1 / 4 + q) + (1 / 4 - q)) + ((1 / 4 + q) + (1 / 4 - q)) * Real.log 2) := by
  unfold lineStat
  rw [alternatives_s₀, sum_pair r₁_ne_r₂, sum_pair r₁_ne_r₂, cls_r₁, cls_r₂]
  rfl

/-- **The non-centrality parameter of the false null tends to zero**: the line statistic of the law tends to `0` as `q → 0`. -/
theorem exists_lineStat_lt {d : ℝ} (hd : 0 < d) : ∃ q : ℝ, 0 < q ∧ q < 1 / 4 ∧ lineStat (fun s => wt q (cls s)) s₀ < d := by
  have hcont : Continuous fun q : ℝ => lineStat (fun s => wt q (cls s)) s₀ := by
    refine (continuous_lineStat s₀).comp (continuous_pi fun s => ?_)
    have hcl : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hcl (cls s) with h | h | h <;> rw [h] <;> simp only [wt]
    · exact continuous_const
    · show Continuous fun q : ℝ => 1 / 4 + q
      fun_prop
    · show Continuous fun q : ℝ => 1 / 4 - q
      fun_prop
  have hval : lineStat (fun s => wt 0 (cls s)) s₀ = 0 := by
    rw [lineStat_wt]
    have h₁ : Real.log (1 / 4 + 0) = -(2 * Real.log 2) := by
      rw [show (1 / 4 + 0 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      norm_num
    have h₂ : Real.log (1 / 4 - 0) = -(2 * Real.log 2) := by
      rw [show (1 / 4 - 0 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      norm_num
    have h₃ : Real.log ((1 / 4 + 0) + (1 / 4 - 0)) = -Real.log 2 := by
      rw [show ((1 / 4 + 0) + (1 / 4 - 0) : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    rw [h₁, h₂, h₃]
    ring
  have hev : ∀ᶠ q in 𝓝 (0 : ℝ), lineStat (fun s => wt q (cls s)) s₀ < d :=
    hcont.continuousAt.eventually_lt continuousAt_const (by rw [hval]; exact hd)
  obtain ⟨q, hq, hq'⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
  exact ⟨q, hq'.1, hq'.2, hq⟩

/-- A quartet tree displayed by a subtree of `T₀` is `01|23`. -/
theorem eq_s₀_of_displays {T : Finset (Finset (Fin 4))} (hT : T ⊆ OnFour.T₀) {s : QuartetTree (Fin 4)} (h : Displays T s) : s = s₀ := by
  obtain ⟨A, hA, hAs⟩ := h
  have hD : Displays (OnFour.gene 0).1 s := ⟨A, hT hA, hAs⟩
  have hmem : ({0, 1} : Finset (Fin 4)) ∈ s.val := by
    rcases cases_val s with ⟨B, C, hs, ht, hm, -⟩ | ⟨B, C, hs, ht, -, -, h₀, -⟩ | ⟨B, C, hs, ht, -, -, -, h₀, -⟩
    · exact (mem_val_iff hs).2 hm
    · exact absurd ((displays_iff_of_val hs ht).1 hD) h₀
    · exact absurd ((displays_iff_of_val hs ht).1 hD) h₀
  refine QuartetTree.eq_of_taxa_eq_of_mem (by rw [OnFour.taxa_eq_univ, OnFour.taxa_eq_univ]) hmem ?_
  simp [s₀, quartetTree]

/-- If the T1 p-value of `01|23` reaches the level, every tree in `T₀` has an overall p-value at least the level. -/
theorem le_treeT1P {o : ECToBlobOptions} {α : ℝ} {c : QuartetTree (Fin 4) → ℝ} (hα : α ≤ 1) (hp : α ≤ t1PValue c s₀)
    {T : Finset (Finset (Fin 4))} (hT : T ⊆ OnFour.T₀) : α ≤ treeT1P o c T := by
  unfold treeT1P
  set P := (univ.filter fun s => Displays T s).val.map fun s => t1PValue c s with hP
  by_cases h0 : P = 0
  · rw [h0]
    unfold combineP
    simpa using hα
  · have h01 : ∀ x ∈ P, 0 ≤ x ∧ x ≤ 1 := by
      intro x hx
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
      exact ⟨(t1PValue_pos _ _).le, Trinomial.t1Tail_le_one _ _⟩
    refine le_trans ?_ (minP_le_combineP o.testCo h0 h01)
    obtain ⟨s, hs, hsv⟩ := Multiset.mem_map.1 (minP_mem h0 fun x hx => (h01 x hx).2)
    rw [← hsv, eq_s₀_of_displays hT (mem_filter.1 hs).2]
    exact hp

/-- (`ecto:cutoff_alpha`) **Lines 1164-1167: "we also need `o(n)` cutoff values", for `α_n`.** On the 4-sunlet, with `T₀` having the false edge
`01|23`, suppose that `log β_n / n → 0` and that the output is the tree of blobs with probability tending to one, on all the laws
`(1/2, 1/4 + q, 1/4 - q)`, for levels `α_n` in `(0, 1]`. Then `log α_n / n → 0`. Otherwise, at a small `q`, the star test rejects and the T1
test of the false null doesn't. This holds for all the options of the algorithm. -/
theorem tendsto_log_alpha_of_consistent {α β : ℕ → ℝ} (hα₀ : ∀ᶠ n in atTop, 0 < α n) (hα₁ : ∀ᶠ n in atTop, α n ≤ 1)
    (hβ₀ : Tendsto β atTop (𝓝[>] 0)) (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) {o : ECToBlobOptions}
    (h : ∀ q : ℝ, 0 < q → q < 1 / 4 → Tendsto (fun n => iidProb (law q) n fun ω =>
      ectoblob o (α n) (β n) (quartetCount Subtype.val ω) OnFour.T₀ = treeOfBlobs net) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set d : ℝ := -a / 2 with hddef
    have hd0 : 0 < d := by rw [hddef]; linarith
    obtain ⟨q, hq0, hq1, hq⟩ := exists_lineStat_lt hd0
    have hd := law_isDist hq0 hq1
    have hp : displayCF (law q) Subtype.val = fun s => wt q (cls s) := funext (displayCF_law q)
    have hF : ∀ᶠ x in 𝓝 (displayCF (law q) Subtype.val),
        lineStat x s₀ < d ∧ (∑ r ∈ s₀.alternatives, x r) / 2 < x s₀ := by
      rw [hp]
      refine ((continuous_lineStat s₀).continuousAt.eventually_lt continuousAt_const hq).and ?_
      have hc₁ : Continuous fun x : QuartetTree (Fin 4) → ℝ => (∑ r ∈ s₀.alternatives, x r) / 2 :=
        (continuous_finsetSum _ fun r _ => continuous_apply r).div_const 2
      refine hc₁.continuousAt.eventually_lt (continuous_apply s₀).continuousAt ?_
      show (∑ r ∈ s₀.alternatives, wt q (cls r)) / 2 < wt q (cls s₀)
      rw [alternatives_s₀, sum_pair r₁_ne_r₂, cls_r₁, cls_r₂, cls_s₀]
      show ((1 / 4 + q) + (1 / 4 - q)) / 2 < 1 / 2
      linarith
    have hlln := tendsto_iidProb_freq (sides := (Subtype.val : BinaryGeneTree (Fin 4) → _)) hd hF
    have hnu : ∀ B ∈ internalSides OnFour.T₀, ∀ s ∈ multipartitionQuartets OnFour.T₀ B,
        ¬ IsUniformOn (displayCF (law q) Subtype.val) s.taxa := by
      intro B _ s _ hu
      have hv := hu s₀ (mem_treesOn.2 (by rw [OnFour.taxa_eq_univ, OnFour.taxa_eq_univ]))
      rw [displayCF_law, cls_s₀] at hv
      simp only [wt] at hv
      norm_num at hv
    have hstar := eventually_afterStar_eq_binary hd o OnFour.T₀_isUnrootedTree hnu hβ₀ hβ (ε := 1 / 4) (by norm_num)
    have ev₁ := hlln.eventually_const_lt (show (3 : ℝ) / 4 < 1 by norm_num)
    have ev₂ := (h q hq0 hq1).eventually_const_lt (show (3 : ℝ) / 4 < 1 by norm_num)
    set K : ℝ := Real.log (√(2 * Real.pi)) + 1 with hK
    have ev₃ : ∀ᶠ n : ℕ in atTop, K < n * d := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (K / d)
      filter_upwards [this] with n hn
      rwa [div_lt_iff₀ hd0] at hn
    filter_upwards [ev₁, ev₂, hstar, hα₀, hα₁, ev₃, eventually_gt_atTop 0] with n h₁ h₂ h₃ hpos hle hK' hn
    have hand₁ := iidProb_and_ge' hd n (fun ω => ectoblob o (α n) (β n) (quartetCount Subtype.val ω) OnFour.T₀ = treeOfBlobs net)
      (fun ω => lineStat (fun r => quartetCount Subtype.val ω r / n) s₀ < d ∧
        (∑ r ∈ s₀.alternatives, quartetCount Subtype.val ω r / n) / 2 < quartetCount Subtype.val ω s₀ / n)
    have hand₂ := iidProb_and_ge' hd n (fun ω => ectoblob o (α n) (β n) (quartetCount Subtype.val ω) OnFour.T₀ = treeOfBlobs net ∧
        (lineStat (fun r => quartetCount Subtype.val ω r / n) s₀ < d ∧
          (∑ r ∈ s₀.alternatives, quartetCount Subtype.val ω r / n) / 2 < quartetCount Subtype.val ω s₀ / n))
      (fun ω => afterStar o (β n) (quartetCount Subtype.val ω) OnFour.T₀ = OnFour.T₀)
    obtain ⟨ω, ⟨hω₁, hω₂, hω₃⟩, hω₄⟩ := exists_of_iidProb_pos (lt_of_lt_of_le (by linarith) hand₂)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set c := quartetCount (Subtype.val : BinaryGeneTree (Fin 4) → _) ω with hc
    -- the statistic is below `n d`
    have hstat : t1Stat c s₀ < n * d := by
      have heq : c = fun r => (n : ℝ) * (c r / n) := by
        funext r
        field_simp
      rw [heq, t1Stat_const_mul hn']
      refine mul_lt_mul_of_pos_left ?_ hn'
      unfold t1Stat
      rw [ite_eq_left hω₃.le]
      exact hω₂
    -- so the T1 test can't reach the level
    have hlt : t1PValue c s₀ < α n := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ i, α n ≤ treeT1P o c (treeSeq o (β n) c OnFour.T₀ i) := fun i =>
        le_treeT1P hle hcon ((treeSeq_subset_afterStar i).trans (by rw [hω₄]))
      rw [ectoblob_eq_afterStar_of_forall_le hall, hω₄] at hω₁
      exact T₀_ne hω₁
    have hlow : chiSqOneTail (n * d) ≤ t1PValue c s₀ :=
      (Trinomial.chiSqOneTail_anti hstat.le).trans (chiSqOneTail_le_t1Tail _ _)
    have hlog : -Real.log (√(2 * Real.pi)) - 1 - n * d < Real.log (α n) :=
      lt_of_le_of_lt (log_chiSqOneTail_ge (by positivity))
        (Real.log_lt_log (chiSqOneTail_pos _) (hlow.trans_lt hlt))
    rw [lt_div_iff₀ hn']
    have ha' : a = -(2 * d) := by rw [hddef]; ring
    rw [ha']
    nlinarith
  · filter_upwards [hα₀, hα₁] with n hpos hle
    have : Real.log (α n) ≤ 0 := Real.log_nonpos hpos.le hle
    exact (div_nonpos_of_nonpos_of_nonneg this (Nat.cast_nonneg _)).trans_lt ha

end OnBlob

/-- (`ecto:cutoff_levels`) **Lines 1164-1167, both levels: "we also need `o(n)` cutoff values".** Levels in `(0, 1)` with `β_n → 0` that give the
conclusion of Theorem 8.2, for all the laws of binary gene trees that meet both directions of Assumption 1, with the option `o` for which
the combination is `Bon` or the alternatives are positive, have `log α_n / n → 0` and `log β_n / n → 0`. -/
theorem tendsto_log_levels_of_valid {α β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 0)) (hα₀ : ∀ᶠ n in atTop, 0 < α n ∧ α n < 1)
    (hβ₀ : ∀ᶠ n in atTop, 0 < β n ∧ β n < 1)
    (h : ∀ {V E X : Type} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X) (_ : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ)
      (_ : IsDist dist) (_ : Assumption1Forward N (displayCF dist Subtype.val)) (_ : Assumption1Converse N (displayCF dist Subtype.val))
      (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
      (_ : (o.testCo = .cauchy ∨ o.testCo = .cbc) → ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r),
      Tendsto (fun n => iidProb dist n fun ω =>
        ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0) ∧ Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) := by
  let o : ECToBlobOptions := ⟨.bi, .bon, .early, .lrt⟩
  have hbon : ¬ (o.testCo = .cauchy ∨ o.testCo = .cbc) := by simp [o]
  have hlβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) := by
    refine OnFour.tendsto_log_beta_of_consistent (α := α) (o := o) (hβ₀.mono fun _ hn => hn.1) (hβ₀.mono fun _ hn => hn.2.le) rfl
      fun q hq0 hq1 => ?_
    obtain ⟨h₁, h₂⟩ := OnFour.law_assumption1 hq1
    refine h OnFour.net OnFour.net_isPhylogenetic _ (OnFour.law_isDist hq0.le hq1) h₁ h₂ OnFour.T₀ ⟨OnFour.T₀_isUnrootedTree, ?_⟩ o
      fun hm => absurd hm hbon
    rw [OnFour.treeOfBlobs_eq]
  refine ⟨?_, hlβ⟩
  have hβ' : Tendsto β atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hβ, hβ₀.mono fun _ hn => hn.1⟩
  refine OnBlob.tendsto_log_alpha_of_consistent (o := o) (hα₀.mono fun _ hn => hn.1) (hα₀.mono fun _ hn => hn.2.le) hβ' hlβ
    fun q hq0 hq1 => ?_
  obtain ⟨h₁, h₂⟩ := OnBlob.law_assumption1 hq0 hq1
  exact h OnBlob.net OnBlob.net_isPhylogenetic _ (OnBlob.law_isDist hq0 hq1) h₁ h₂ OnFour.T₀ OnBlob.isResolutionOf_T₀ o
    fun hm => absurd hm hbon

end ECToBlob.BinaryLaw
