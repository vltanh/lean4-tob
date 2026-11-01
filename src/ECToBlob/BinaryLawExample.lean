module

public import ECToBlob.DisplayedTreeExample

/-!
# Two laws of binary gene trees on the network of `FinNetwork.Binary`

* **E11 of the report, in Lean: Theorem 8.2 without its hypothesis on the alternatives fails for Cauchy and CBC, at all
  sequences** (`not_theorem8_2_without_hpos`). The law `lawD` is that of the two displayed trees, with weights `1/2`. Its
  quartets with a cut split have concordance factors `(1, 0, 0)`, so T1 p-values `1`, and Cauchy and CBC keep the false edge. A
  sequence `β_n` that were valid on all models would have `o(n)` cutoffs (`tendsto_log_beta_of_consistent`, by a family of
  laws on a tree on four taxa, lines 1164-1167 of the paper), and at such a level the star test keeps `T₀`.
* **ECToBlob §10: combining the edge p-values under CBC fails** (`not_consistency_edge_combination_cbc`). The law `lawC` has
  positive alternatives, it meets both directions of Assumption 1, and all the other variants are consistent on it
  (`ECToBlob.Remarks.consistency_edge_combination`). The p-values of the quartets of the cut edge `de` are equal on every
  sample, and asymptotically uniform. So with probability about `1/2` they are above `1/2`, the Bonferroni p-value of the edge is
  `1`, its CBC p-value is `1`, and the CBC combination with a `1` is `1` (`ECToBlob.Remarks.combineP_cbc_eq_one`). The tree `T₀`
  with the false edge `bc` is then not rejected. This is the argument at `ECToBlob.Remarks.tendsto_ectoblobEdge_limitTree`, on this law.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob.BinaryLaw

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.FalseEdge ECToBlob.Framework
open ECToBlob.DisplayedTree ECToBlob.FinNetwork ECToBlob.Remarks

/-! ### Laws with finite support -/

section PointLaw

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ}

/-- The law that gives the gene tree `gene i` the weight `w i`. -/
def pointLaw (gene : Fin k → BinaryGeneTree X) (w : Fin k → ℝ) (g : BinaryGeneTree X) : ℝ :=
  ∑ i, if g = gene i then w i else 0

variable {gene : Fin k → BinaryGeneTree X} {w : Fin k → ℝ}

theorem pointLaw_isDist (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) : IsDist (pointLaw gene w) := by
  refine ⟨fun g => Finset.sum_nonneg fun i _ => ?_, ?_⟩
  · split_ifs
    · exact h0 i
    · exact le_rfl
  · unfold pointLaw
    rw [Finset.sum_comm]
    simpa using h1

theorem displayCF_pointLaw (s : QuartetTree X) :
    displayCF (pointLaw gene w) Subtype.val s = ∑ i, if Displays (gene i).1 s then w i else 0 := by
  unfold displayCF pointLaw
  have hstep : ∀ g : BinaryGeneTree X, (if Displays g.1 s then ∑ i, (if g = gene i then w i else 0) else 0) =
      ∑ i, if Displays g.1 s then (if g = gene i then w i else 0) else 0 := by
    intro g
    split_ifs <;> simp
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (gene i)]
  · simp
  · intro g _ hg
    simp [hg]
  · intro h
    exact absurd (mem_univ _) h

/-- A gene tree of positive probability is in the list. -/
theorem exists_gene_of_ne_zero {g : BinaryGeneTree X} (h : pointLaw gene w g ≠ 0) :
    ∃ i, g = gene i ∧ w i ≠ 0 := by
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero h
  by_cases hg : g = gene i
  · rw [ite_eq_left hg] at hi
    exact ⟨i, hg, hi⟩
  · exact absurd (ite_eq_right hg) hi

omit [Fintype X] in
/-- Displaying a quartet tree, in terms of its two cherries. -/
theorem displays_iff_of_val {T : Finset (Finset X)} {s : QuartetTree X} {B C : Finset X}
    (hs : s.val = {B, C}) (ht : s.taxa = B ∪ C) :
    Displays T s ↔ ∃ A ∈ T, A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C := by
  unfold Displays
  rw [ht, hs]
  simp only [mem_insert, mem_singleton]

end PointLaw

/-! ### A quartet tree with counts -/

section Counts

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}

/-- The trees on the taxa of `s` are `s` and its alternatives. -/
theorem treesOn_taxa_eq_insert (s : QuartetTree X) : treesOn s.taxa = insert s s.alternatives := by
  ext r
  simp only [treesOn, QuartetTree.alternatives, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro hr
    by_cases hrs : r = s
    · exact Or.inl hrs
    · exact Or.inr ⟨hr, hrs⟩
  · rintro (rfl | hr)
    · rfl
    · exact hr.1

theorem notMem_alternatives (s : QuartetTree X) : s ∉ s.alternatives := by
  simp [QuartetTree.alternatives]

/-- Swapping the alternatives does not change the T1 p-value. -/
theorem t1PValueR_swap (a b c : ℝ) : Trinomial.t1PValueR a b c = Trinomial.t1PValueR a c b := by
  unfold Trinomial.t1PValueR Trinomial.lineS Trinomial.starS
  rw [add_comm b c, add_assoc, add_comm c b, ← add_assoc]
  have h : a * Real.log a + b * Real.log b + c * Real.log c = a * Real.log a + c * Real.log c + b * Real.log b := by
    ring
  have h' : b * Real.log b + c * Real.log c = c * Real.log c + b * Real.log b := by ring
  have h'' : a + c + b = a + b + c := by ring
  simp only [h, h', h'']

end Counts

/-! ### Combining p-values with a `1` -/

/-- Combined p-values of positive p-values are positive. -/
theorem combineP_pos (m : TestCorrection) {P : Multiset ℝ} (h : ∀ p ∈ P, 0 < p ∧ p ≤ 1) :
    0 < combineP m P := by
  by_cases hP : P = 0
  · simp [combineP, hP]
  · have hmin := (h _ (minP_mem hP fun p hp => (h p hp).2)).1
    exact hmin.trans_le (minP_le_combineP m hP fun p hp => ⟨(h p hp).1.le, (h p hp).2⟩)

/-- **The CBC p-value is `1` when the Bonferroni p-value is `1`.** -/
theorem combineP_cbc_eq_one_of_bon {P : Multiset ℝ} (hP : P ≠ 0) (h : ∀ p ∈ P, 0 < p ∧ p ≤ 1)
    (hb : 1 ≤ (Multiset.card P : ℝ) * minP P) : combineP .cbc P = 1 := by
  have hbon : bonP P = 1 := min_eq_left hb
  have hcau : 0 < cauchyP P := by
    have := combineP_pos .cauchy h
    simpa [combineP, hP] using this
  unfold combineP cbcP
  rw [ite_eq_right hP]
  show cauchyP {bonP P, cauchyP P} = 1
  rw [hbon, cauchyP, ite_eq_right, ite_eq_left]
  · simp [Multiset.insert_eq_cons]
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hcau.ne⟩

/-! ### Assumption 1 on the network -/

namespace OnBinary

open FinNetwork.Binary

/-- A cut split of an induced network of this network is `de|xy`. -/
theorem mem_val_of_inducedCutSplit {s : QuartetTree (Fin 5)} (h : InducedCutSplit net s) :
    ({3, 4} : Finset (Fin 5)) ∈ s.val := by
  obtain ⟨a, b, c, d, hc, rfl, hr⟩ := exists_rdom_of_inducedCutSplit net_isPhylogenetic h
  have hdec : ∀ a b c d : Fin 5, ({a, b, c, d} : Finset (Fin 5)).card = 4 →
      RDomT tgt lf desc avoid a b c d →
      ({a, b} : Finset (Fin 5)) = {3, 4} ∨ ({c, d} : Finset (Fin 5)) = {3, 4} := by decide
  rcases hdec a b c d hc (tables.rdom_iff.1 hr) with h' | h'
  · simp [quartetTree, h']
  · simp [quartetTree, h']

/-- A quartet tree with the cherry `de` is a cut split. -/
theorem inducedCutSplit_of_mem_val {s : QuartetTree (Fin 5)} (h : ({3, 4} : Finset (Fin 5)) ∈ s.val) :
    InducedCutSplit net s :=
  inducedCutSplit_of_mem net_isPhylogenetic ((mem_treeOfBlobs_iff (A := {3, 4})).2 (by decide))
    (by rwa [Finset.inter_eq_left.2 (s.subset_taxa h)])

/-- Both directions of Assumption 1, for concordance factors of the shape of the two laws below. -/
theorem assumption1_of_shape {p : QuartetTree (Fin 5) → ℝ} {A B C D : ℝ} (hAB : B < A) (hC : 0 < C)
    (hD : 0 < D)
    (hcut : ∀ s : QuartetTree (Fin 5), ({3, 4} : Finset (Fin 5)) ∈ s.val → p s = A)
    (halt : ∀ s : QuartetTree (Fin 5), ({3, 4} : Finset (Fin 5)) ∉ s.val →
      ({3, 4} : Finset (Fin 5)) ⊆ s.taxa → p s = B)
    (hbc : ∀ s : QuartetTree (Fin 5), ({1, 2} : Finset (Fin 5)) ∈ s.val →
      ¬ ({3, 4} : Finset (Fin 5)) ⊆ s.taxa → p s = C)
    (hac : ∀ s : QuartetTree (Fin 5), ({0, 2} : Finset (Fin 5)) ∈ s.val →
      ¬ ({3, 4} : Finset (Fin 5)) ⊆ s.taxa → p s = D)
    (hab : ∀ s : QuartetTree (Fin 5), ({0, 1} : Finset (Fin 5)) ∈ s.val →
      ¬ ({3, 4} : Finset (Fin 5)) ⊆ s.taxa → p s = 0) :
    Assumption1Forward net p ∧ Assumption1Converse net p := by
  have hN := net_isPhylogenetic
  have hF : Assumption1Forward net p := by
    refine ⟨fun q hq htr => absurd htr (not_hasTrivialFourBlob hq), fun s hs => ?_⟩
    have h₀ := mem_val_of_inducedCutSplit hs
    have haltv : ∀ r ∈ s.alternatives, p r = B := by
      intro r hr
      obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
      exact halt r (fun h => hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt h h₀)) (hrt ▸ s.subset_taxa h₀)
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · rw [haltv r hr, hcut s h₀]
      exact hAB
    · rw [haltv r hr, haltv r' hr']
  refine ⟨hF, assumption1Converse_of_cases hF fun q hq => ?_⟩
  have hcases : ∀ q : Finset (Fin 5), q.card = 4 →
      (∃ y z : Fin 5, q = {3, 4, y, z}) ∨ ∃ x : Fin 5, (x = 3 ∨ x = 4) ∧ q = {0, 1, 2, x} := by decide
  rcases hcases q hq with ⟨y, z, rfl⟩ | ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inl ⟨quartetTree 3 4 y z hq, by simp [treesOn],
      inducedCutSplit_of_mem_val (by simp)⟩)
  · right; right
    have h₁' : ({0, 2, 1, x} : Finset (Fin 5)).card = 4 := by
      rcases hx with rfl | rfl <;> decide
    have h₂' : ({1, 2, 0, x} : Finset (Fin 5)).card = 4 := by
      rcases hx with rfl | rfl <;> decide
    have ht₁ : ({0, 2, 1, x} : Finset (Fin 5)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have ht₂ : ({1, 2, 0, x} : Finset (Fin 5)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have hn : ¬ ({3, 4} : Finset (Fin 5)) ⊆ {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have hm₁ : quartetTree 0 2 1 x h₁' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree, ht₁]
    have hm₂ : quartetTree 1 2 0 x h₂' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree, ht₂]
    have hm₃ : quartetTree 0 1 2 x hq ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [taxa_quartetTree]
    have h12 : quartetTree 0 2 1 x h₁' ≠ quartetTree 1 2 0 x h₂' := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    have h13 : quartetTree 0 2 1 x h₁' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    have h23 : quartetTree 1 2 0 x h₂' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    refine ⟨_, hm₁, _, hm₂, _, hm₃, h12, h13, h23, ?_, ?_, ?_⟩
    · exact hab _ (by simp) (by rwa [taxa_quartetTree])
    · rw [hac _ (by simp) (by rwa [taxa_quartetTree, ht₁])]
      exact hD
    · rw [hbc _ (by simp) (by rwa [taxa_quartetTree, ht₂])]
      exact hC

/-! ### The gene trees of the two laws -/

/-- The clusters of the gene trees: the singletons, and three more clusters. -/
def clusters (P Q R : Finset (Fin 5)) : Finset (Finset (Fin 5)) :=
  {univ, {0}, {1}, {2}, {3}, {4}, P, Q, R}

/-- The rooted binary trees `((x,y),(z,(u,v)))`, from their clusters `P = {x,y}`, `Q = {u,v}` and `R = {z,u,v}`. -/
def hierD : Fin 2 → Finset (Finset (Fin 5)) :=
  ![clusters {3, 4} {1, 2} {0, 1, 2}, clusters {3, 4} {0, 2} {0, 1, 2}]

/-- The two displayed trees of the network: `((d,e),(a,(b,c)))` and `((d,e),(b,(a,c)))`. -/
def geneD (i : Fin 2) : BinaryGeneTree (Fin 5) :=
  ⟨unroot (hierD i), hierD i, by unfold IsHierarchy; revert i; decide, rfl, by revert i; decide⟩

/-- **The law of the displayed trees**, with the weights `1/2`. -/
def lawD : BinaryGeneTree (Fin 5) → ℝ := pointLaw geneD fun _ => 1 / 2

theorem lawD_isDist : IsDist lawD :=
  pointLaw_isDist (fun _ => by norm_num) (by simp)

/-- The number of displayed trees displaying the quartet tree with cherries `B`, `C`. -/
def countD (B C : Finset (Fin 5)) : ℕ :=
  ∑ i, if ∃ A ∈ unroot (hierD i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C then 1 else 0

theorem countD_eq : ∀ B ∈ powersetCard 2 (univ : Finset (Fin 5)),
    ∀ C ∈ powersetCard 2 (univ : Finset (Fin 5)), Disjoint B C →
      countD B C = if B = {3, 4} ∨ C = {3, 4} then 2 else if ({3, 4} : Finset (Fin 5)) ⊆ B ∪ C then 0
        else if B = {1, 2} ∨ C = {1, 2} then 1 else if B = {0, 2} ∨ C = {0, 2} then 1 else 0 := by
  decide

/-- The concordance factors of `lawD`. -/
theorem displayCF_lawD (s : QuartetTree (Fin 5)) :
    displayCF lawD Subtype.val s = if ({3, 4} : Finset (Fin 5)) ∈ s.val then 1
      else if ({3, 4} : Finset (Fin 5)) ⊆ s.taxa then 0
      else if ({1, 2} : Finset (Fin 5)) ∈ s.val then 1 / 2
      else if ({0, 2} : Finset (Fin 5)) ∈ s.val then 1 / 2 else 0 := by
  obtain ⟨B, C, hs, hB, hC, hd, ht⟩ := s.exists_eq_pair
  have hsum : displayCF lawD Subtype.val s = (countD B C : ℝ) / 2 := by
    unfold lawD
    rw [displayCF_pointLaw]
    unfold countD
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : Displays (geneD i).1 s ↔ ∃ A ∈ unroot (hierD i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C :=
      displays_iff_of_val hs ht
    simp only [h]
    split_ifs <;> simp
  have hc := countD_eq B (mem_powersetCard.2 ⟨subset_univ _, hB⟩) C
    (mem_powersetCard.2 ⟨subset_univ _, hC⟩) hd
  have hmem : ∀ P : Finset (Fin 5), P ∈ s.val ↔ B = P ∨ C = P := by
    intro P
    rw [hs]
    simp only [mem_insert, mem_singleton]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  rw [hsum, hc, ht]
  simp only [hmem]
  split_ifs <;> norm_num

theorem lawD_assumption1 :
    Assumption1Forward net (displayCF lawD Subtype.val) ∧
      Assumption1Converse net (displayCF lawD Subtype.val) := by
  refine assumption1_of_shape (A := 1) (B := 0) (C := 1 / 2) (D := 1 / 2) one_pos (by norm_num)
    (by norm_num) (fun s h => ?_) (fun s h h' => ?_) (fun s h h' => ?_) (fun s h h' => ?_)
    (fun s h h' => ?_)
  · rw [displayCF_lawD, ite_eq_left h]
  · rw [displayCF_lawD, ite_eq_right h, ite_eq_left h']
  · have hn : ({3, 4} : Finset (Fin 5)) ∉ s.val := fun h₃ => h' (s.subset_taxa h₃)
    rw [displayCF_lawD, ite_eq_right hn, ite_eq_right h', ite_eq_left h]
  · have hn : ({3, 4} : Finset (Fin 5)) ∉ s.val := fun h₃ => h' (s.subset_taxa h₃)
    have hn' : ({1, 2} : Finset (Fin 5)) ∉ s.val := fun h₃ => by
      have := s.2.2.2 _ h₃ _ h (by decide)
      exact absurd this (by decide)
    rw [displayCF_lawD, ite_eq_right hn, ite_eq_right h', ite_eq_right hn', ite_eq_left h]
  · have hn : ({3, 4} : Finset (Fin 5)) ∉ s.val := fun h₃ => h' (s.subset_taxa h₃)
    have hn' : ({1, 2} : Finset (Fin 5)) ∉ s.val := fun h₃ => by
      have := s.2.2.2 _ h₃ _ h (by decide)
      exact absurd this (by decide)
    have hn'' : ({0, 2} : Finset (Fin 5)) ∉ s.val := fun h₃ => by
      have := s.2.2.2 _ h₃ _ h (by decide)
      exact absurd this (by decide)
    rw [displayCF_lawD, ite_eq_right hn, ite_eq_right h', ite_eq_right hn', ite_eq_right hn'']

end OnBinary

/-! ### The star test on binary gene trees, at any level -/

section Star

variable {X : Type*} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- At an edge of `T₀` none of whose quartets is uniform, the star test rejects with probability tending to one, whichever the
combination method. -/
theorem eventually_edgeStarP_lt_binary (hd : IsDist dist) (o : ECToBlobOptions)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀) {B : Finset X} (hB : 2 ≤ B.card ∧ 2 ≤ Bᶜ.card)
    (hnu : ∀ s ∈ multipartitionQuartets T₀ B, ¬ IsUniformOn (displayCF dist Subtype.val) s.taxa)
    {β : ℕ → ℝ} (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      edgeStarP o (quartetCount Subtype.val ω) T₀ B < β n := by
  obtain ⟨s₀, hs₀⟩ := FalseEdge.exists_mem_multipartitionQuartets
    (isSplitFamily_of_internal hT₀ hB.1) hB.1 hB.2
  have hone := displaysOne_binaryGeneTree dist
  have h := eventually_testCorrect_of_level hd o.testCo hβ₀ (multipartitionQuartets T₀ B) le_rfl
    (fun s => IsUniformOn (displayCF dist Subtype.val) s.taxa)
    (fun s _ ω => starPValue o.starTest (quartetCount Subtype.val ω) s.taxa)
    (fun s _ ω => starPValue_mem' _ (fun r => quartetCount_nonneg ω r) s.card_taxa)
    (fun ε' hε' => ⟨1 / 4, by norm_num, by norm_num, Eventually.of_forall fun n => by
      have hle := iidProb_mono hd (n := n) (Ev := fun _ => True)
        (Ev' := fun ω : Fin n → BinaryGeneTree X => ∀ s ∈ multipartitionQuartets T₀ B,
          IsUniformOn (displayCF dist Subtype.val) s.taxa →
            1 / 4 ≤ starPValue o.starTest (quartetCount Subtype.val ω) s.taxa ∧
              ((o.testCo = .cauchy ∨ o.testCo = .cbc) →
                starPValue o.starTest (quartetCount Subtype.val ω) s.taxa ≤ 1 - 1 / 4))
        (fun ω _ s hs hu => absurd hu (hnu s hs))
      rw [iidProb_true hd] at hle
      linarith⟩)
    (fun s _ hs c hc => tendsto_lt_level_of_growth (hβ₀.eventually self_mem_nhdsWithin) hβ
      (fun b hb => starStat_growth o.starTest hd hone s.card_taxa hs hb) hc) hε
  filter_upwards [h] with n hn
  exact hn.trans_le (iidProb_mono hd fun ω hω => hω.2 ⟨s₀, hs₀, hnu s₀ hs₀⟩)

/-- All the star tests reject, with probability tending to one, if no quartet around an edge of `T₀` is uniform. -/
theorem eventually_afterStar_eq_binary (hd : IsDist dist) (o : ECToBlobOptions)
    {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀)
    (hnu : ∀ B ∈ internalSides T₀, ∀ s ∈ multipartitionQuartets T₀ B,
      ¬ IsUniformOn (displayCF dist Subtype.val) s.taxa)
    {β : ℕ → ℝ} (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      afterStar o (β n) (quartetCount Subtype.val ω) T₀ = T₀ := by
  have hall := eventually_forall_mem hd (internalSides T₀)
    (fun B n ω => edgeStarP o (quartetCount Subtype.val ω) T₀ B < β n) hε
    fun B hB ε' hε' => eventually_edgeStarP_lt_binary hd o hT₀ (mem_internalSides.1 hB).2 (hnu B hB)
      hβ₀ hβ hε'
  filter_upwards [hall] with n hn
  refine hn.trans_le (iidProb_mono hd fun ω hstar => ?_)
  refine Finset.filter_true_of_mem fun B _ => ⟨fun hB => ?_, fun hB => ?_⟩
  · exact absurd (mem_filter.1 hB).2 (not_lt_of_gt (hstar B (mem_filter.1 hB).1))
  · exact absurd (mem_filter.1 hB).2 (not_lt_of_gt (hstar _ (mem_filter.1 hB).1))

end Star

/-- A positive probability gives a sample. -/
theorem exists_of_iidProb_pos {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {n : ℕ}
    {Ev : (Fin n → Γ) → Prop} (h : 0 < iidProb dist n Ev) : ∃ ω, Ev ω := by
  by_contra hcon
  push Not at hcon
  have : iidProb dist n Ev = 0 := Finset.sum_eq_zero fun ω _ => ite_eq_right (hcon ω)
  linarith

/-- With probability one the product of the weights of the draws is not zero. -/
theorem prod_ne_zero_of_forall {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {n : ℕ} {ω : Fin n → Γ}
    (h : ∀ i, dist (ω i) ≠ 0) : ∏ i, dist (ω i) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => h i

/-! ### The law of the displayed trees, with Cauchy and CBC -/

namespace OnBinary

open FinNetwork.Binary

/-- A quartet tree of the bipartition of `de` has the cherry `de`. -/
theorem mem_val_of_mem_bipartition {s : QuartetTree (Fin 5)}
    (hs : s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5))) : ({3, 4} : Finset (Fin 5)) ∈ s.val := by
  have h₁ := (mem_filter.1 hs).2
  have h₂ : (({3, 4} : Finset (Fin 5)) ∩ s.taxa).card = 2 := s.card_of_mem h₁
  have h₃ : ({3, 4} : Finset (Fin 5)) ∩ s.taxa = {3, 4} :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h₂]; decide)
  rwa [h₃] at h₁

theorem T₀_internal_de : ({3, 4} : Finset (Fin 5)) ∈ T₀ := by unfold T₀ H₀ unroot; decide

/-- **E11 of the report: on the law of the displayed trees, Cauchy and CBC output `T₀`**, with its false edge, with probability
tending to one, at any levels `α_n ≤ 1`, `β_n → 0` from above with `o(n)` cutoffs, for all the quartet types and selection rules. -/
theorem tendsto_lawD_self {o : ECToBlobOptions} (hm : o.testCo = .cauchy ∨ o.testCo = .cbc)
    {α β : ℕ → ℝ} (hα : ∀ᶠ n in atTop, α n ≤ 1) (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb lawD n fun ω =>
      ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = T₀) atTop (𝓝 1) := by
  have hd := lawD_isDist
  obtain ⟨h₁, h₂⟩ := lawD_assumption1
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  swap
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha
  have hε : 0 < 1 - a := by linarith
  have hstar := eventually_afterStar_eq_binary hd o T₀_isUnrootedTree
    (fun B _ s _ hu => not_hasTrivialFourBlob s.card_taxa ((uniform_iff h₁ h₂ s).1 hu)) hβ₀ hβ hε
  filter_upwards [hstar, hα] with n hn hαn
  have hforall := iidProb_forall_ne_zero hd n
  have hand := iidProb_and_ge' hd n (fun ω => afterStar o (β n) (quartetCount Subtype.val ω) T₀ = T₀)
    (fun ω => ∀ i, lawD (ω i) ≠ 0)
  rw [hforall] at hand
  refine (by linarith : a < _).trans_le (iidProb_mono hd fun ω hω => ?_)
  obtain ⟨hafter, hpos⟩ := hω
  have hzero : ∀ s : QuartetTree (Fin 5), ({3, 4} : Finset (Fin 5)) ∈ s.val →
      ∀ r ∈ s.alternatives, displayCF lawD Subtype.val r = 0 := by
    intro s h₀ r hr
    obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
    rw [displayCF_lawD, ite_eq_right (fun h => hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt h h₀)),
      ite_eq_left (hrt ▸ s.subset_taxa h₀)]
  show ectoblobBy o _ _ _ _ _ = _
  rw [ectoblobBy_eq_afterStarBy hm hαn
    (fun _ => ⟨t1PValue_pos _ _, Trinomial.t1Tail_le_one _ _⟩) T₀_isUnrootedTree
    (A := {3, 4}) (by decide) (by show _ ∈ afterStar o _ _ _; rw [hafter]; exact T₀_internal_de)
    (fun s hs => t1PValue_degenerate hd (hzero s (mem_val_of_mem_bipartition hs)) ω
      (prod_ne_zero_of_forall hpos))]
  exact hafter

end OnBinary

/-! ### A family of laws on a tree on four taxa: the cutoffs are `o(n)` -/

namespace OnFour

/-- The tails of the arcs of the tree `((0,1),(2,3))`. -/
def src : Fin 6 → Fin 7 := ![6, 6, 4, 4, 5, 5]

/-- The heads of the arcs. -/
def tgt : Fin 6 → Fin 7 := ![4, 5, 0, 1, 2, 3]

/-- The taxa, as vertices. -/
def lf : Fin 4 → Fin 7 := ![0, 1, 2, 3]

/-- What each vertex reaches. -/
def desc : Fin 7 → Finset (Fin 7) := ![{0}, {1}, {2}, {3}, {0, 1, 4}, {2, 3, 5}, {0, 1, 2, 3, 4, 5, 6}]

/-- What the root reaches off each arc. -/
def avoid : Fin 6 → Finset (Fin 7) :=
  ![{2, 3, 5, 6}, {0, 1, 4, 6}, {1, 2, 3, 4, 5, 6}, {0, 2, 3, 4, 5, 6}, {0, 1, 3, 4, 5, 6},
    {0, 1, 2, 4, 5, 6}]

theorem tables : Tables src tgt 6 desc avoid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The rooted binary tree `((0,1),(2,3))`, as a network. -/
abbrev net : RootedNetwork (Fin 7) (Fin 6) (Fin 4) := FinNetwork.net src tgt 6 lf

theorem net_isPhylogenetic : net.IsPhylogenetic :=
  isPhylogenetic_of_down (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The rooted trees on four taxa with the given cherries. -/
def hier : Fin 3 → Finset (Finset (Fin 4)) :=
  ![{univ, {0}, {1}, {2}, {3}, {0, 1}, {2, 3}}, {univ, {0}, {1}, {2}, {3}, {0, 2}, {1, 3}},
    {univ, {0}, {1}, {2}, {3}, {0, 3}, {1, 2}}]

/-- The three binary trees on four taxa. -/
def gene (i : Fin 3) : BinaryGeneTree (Fin 4) :=
  ⟨unroot (hier i), hier i, by unfold IsHierarchy; revert i; decide, rfl, by revert i; decide⟩

/-- The tree `T₀ = T_B`. -/
def T₀ : Finset (Finset (Fin 4)) := unroot (hier 0)

theorem treeOfBlobs_eq : treeOfBlobs net = T₀ := by
  ext A
  rw [tables.mem_treeOfBlobs_iff net_isPhylogenetic]
  unfold T₀ hier unroot
  revert A
  decide

theorem T₀_isUnrootedTree : IsUnrootedTree T₀ := ⟨hier 0, by unfold IsHierarchy hier; decide, rfl⟩

/-- **The law `(1 - 2q, q, q)`** on the three binary trees on four taxa. For `q` near `1/3` it is near the centroid. -/
def law (q : ℝ) : BinaryGeneTree (Fin 4) → ℝ := pointLaw gene ![1 - 2 * q, q, q]

theorem law_isDist {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1 / 3) : IsDist (law q) := by
  refine pointLaw_isDist (fun i => ?_) ?_
  · fin_cases i
    · show 0 ≤ 1 - 2 * q
      linarith
    · exact h0
    · exact h0
  · rw [Fin.sum_univ_three]
    show 1 - 2 * q + q + q = 1
    ring

/-- The gene trees displaying the quartet tree with cherries `B`, `C`. -/
def dsp (i : Fin 3) (B C : Finset (Fin 4)) : Prop :=
  ∃ A ∈ unroot (hier i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C

instance (i : Fin 3) (B C : Finset (Fin 4)) : Decidable (dsp i B C) :=
  inferInstanceAs (Decidable (∃ A ∈ unroot (hier i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C))

theorem dsp_eq : ∀ B ∈ powersetCard 2 (univ : Finset (Fin 4)),
    ∀ C ∈ powersetCard 2 (univ : Finset (Fin 4)), Disjoint B C →
      if B = {0, 1} ∨ C = {0, 1} then dsp 0 B C ∧ ¬ dsp 1 B C ∧ ¬ dsp 2 B C
      else (¬ dsp 0 B C ∧ dsp 1 B C ∧ ¬ dsp 2 B C) ∨ (¬ dsp 0 B C ∧ ¬ dsp 1 B C ∧ dsp 2 B C) := by
  decide

/-- The concordance factors of the law. -/
def pq (q : ℝ) (s : QuartetTree (Fin 4)) : ℝ := if ({0, 1} : Finset (Fin 4)) ∈ s.val then 1 - 2 * q else q

theorem displayCF_law (q : ℝ) (s : QuartetTree (Fin 4)) : displayCF (law q) Subtype.val s = pq q s := by
  obtain ⟨B, C, hs, hB, hC, hd, ht⟩ := s.exists_eq_pair
  unfold law pq
  rw [displayCF_pointLaw, Fin.sum_univ_three]
  have hdisp : ∀ i, Displays (gene i).1 s ↔ dsp i B C := fun i => displays_iff_of_val hs ht
  have hval : ({0, 1} : Finset (Fin 4)) ∈ s.val ↔ B = {0, 1} ∨ C = {0, 1} := by
    rw [hs]
    simp only [mem_insert, mem_singleton]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  simp only [hdisp, hval]
  have h := dsp_eq B (mem_powersetCard.2 ⟨subset_univ _, hB⟩) C (mem_powersetCard.2 ⟨subset_univ _, hC⟩) hd
  by_cases h₀ : B = {0, 1} ∨ C = {0, 1}
  · rw [ite_eq_left h₀] at *
    obtain ⟨h₁, h₂, h₃⟩ := h
    simp [h₁, h₂, h₃]
  · rw [ite_eq_right h₀] at *
    rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ <;> simp [h₁, h₂, h₃]

/-- The taxa of a quartet tree on four taxa are all of them. -/
theorem taxa_eq_univ (s : QuartetTree (Fin 4)) : s.taxa = univ :=
  Finset.eq_univ_of_card _ (by rw [s.card_taxa]; rfl)

/-- A cut split of the tree is `01|23`. -/
theorem mem_val_of_inducedCutSplit {s : QuartetTree (Fin 4)} (h : InducedCutSplit net s) :
    ({0, 1} : Finset (Fin 4)) ∈ s.val := by
  obtain ⟨a, b, c, d, hc, rfl, hr⟩ := exists_rdom_of_inducedCutSplit net_isPhylogenetic h
  have hdec : ∀ a b c d : Fin 4, ({a, b, c, d} : Finset (Fin 4)).card = 4 →
      RDomT tgt lf desc avoid a b c d →
      ({a, b} : Finset (Fin 4)) = {0, 1} ∨ ({c, d} : Finset (Fin 4)) = {0, 1} := by decide
  rcases hdec a b c d hc (tables.rdom_iff.1 hr) with h' | h'
  · simp [quartetTree, h']
  · simp [quartetTree, h']

/-- Both directions of Assumption 1 hold for the law, at `q < 1/3`. -/
theorem law_assumption1 {q : ℝ} (h1 : q < 1 / 3) :
    Assumption1Forward net (displayCF (law q) Subtype.val) ∧
      Assumption1Converse net (displayCF (law q) Subtype.val) := by
  have hN := net_isPhylogenetic
  have hF : Assumption1Forward net (displayCF (law q) Subtype.val) := by
    refine ⟨fun Q hQ htr => ?_, fun s hs => ?_⟩
    · have : ∀ Q : Finset (Fin 4), Q.card = 4 → ∀ v, ¬ HubT src tgt lf desc avoid Q v := by decide
      obtain ⟨v, hv⟩ := (tables.hasTrivialFourBlob_iff hN hQ).1 htr
      exact absurd hv (this Q hQ v)
    · have h₀ := mem_val_of_inducedCutSplit hs
      have haltv : ∀ r ∈ s.alternatives, displayCF (law q) Subtype.val r = q := by
        intro r hr
        obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
        rw [displayCF_law, pq, ite_eq_right fun h => hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt h h₀)]
      refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
      · rw [haltv r hr, displayCF_law, pq, ite_eq_left h₀]
        linarith
      · rw [haltv r hr, haltv r' hr']
  refine ⟨hF, assumption1Converse_of_cases hF fun Q hQ => Or.inr (Or.inl ?_)⟩
  have hc : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  refine ⟨quartetTree 0 1 2 3 hc, ?_, ?_⟩
  · simp only [treesOn, mem_filter, mem_univ, true_and]
    rw [taxa_eq_univ, Finset.eq_univ_of_card Q (by rw [hQ]; rfl)]
  · exact inducedCutSplit_of_rdom hN hc (tables.rdom_iff.2 (by decide))

/-- The star statistic of the law tends to zero as `q → 1/3`. -/
theorem exists_starStat_lt {d : ℝ} (hd : 0 < d) :
    ∃ q : ℝ, 0 < q ∧ q < 1 / 3 ∧ starStat (pq q) (univ : Finset (Fin 4)) < d := by
  have hcont : Continuous fun q : ℝ => starStat (pq q) (univ : Finset (Fin 4)) := by
    refine (continuous_starStat _).comp (continuous_pi fun s => ?_)
    unfold pq
    split_ifs
    · fun_prop
    · fun_prop
  have hval : starStat (pq (1 / 3)) (univ : Finset (Fin 4)) = 0 := by
    have hc : ∀ r ∈ treesOn (univ : Finset (Fin 4)), pq (1 / 3) r = 1 / 3 := by
      intro r _
      unfold pq
      split_ifs <;> norm_num
    have := starPValue_of_const .lrt (q := (univ : Finset (Fin 4))) (by rfl) hc
    have h₂ : Real.exp (-(starStat (pq (1 / 3)) univ) / 2) = 1 := this
    rw [Real.exp_eq_one_iff] at h₂
    linarith
  have hev : ∀ᶠ q in 𝓝 (1 / 3 : ℝ), starStat (pq q) (univ : Finset (Fin 4)) < d :=
    hcont.continuousAt.eventually_lt continuousAt_const (by rw [hval]; exact hd)
  obtain ⟨q, hq, hq'⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 3))).exists
  exact ⟨q, hq'.1, hq'.2, hq⟩

/-- (`ecto:cutoff_beta`) **Lines 1164-1167: "we also need `o(n)` cutoff values".** If the output with the star test by likelihood ratio is the tree of
blobs with probability tending to one, on all the laws `(1 - 2q, q, q)` on the tree with four taxa, for levels `β_n` in `(0, 1]`, then
`log β_n / n → 0`. Otherwise the star test contracts the edge, at a law near the centroid. -/
theorem tendsto_log_beta_of_consistent {α β : ℕ → ℝ} (hβ₀ : ∀ᶠ n in atTop, 0 < β n)
    (hβ₁ : ∀ᶠ n in atTop, β n ≤ 1) {o : ECToBlobOptions} (ho : o.starTest = .lrt)
    (h : ∀ q : ℝ, 0 < q → q < 1 / 3 → Tendsto (fun n => iidProb (law q) n fun ω =>
      ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs net) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) := by
  have hA : ({0, 1} : Finset (Fin 4)) ∈ T₀ := by unfold T₀ hier unroot; decide
  have hAint : ({0, 1} : Finset (Fin 4)) ∈ internalSides T₀ :=
    mem_internalSides.2 ⟨hA, by decide⟩
  have hcard : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
  obtain ⟨s₀, hs₀⟩ := FalseEdge.exists_mem_multipartitionQuartets (A := {0, 1})
    (isSplitFamily_of_internal T₀_isUnrootedTree (by decide : 2 ≤ ({0, 1} : Finset (Fin 4)).card))
    (by decide) (by decide)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- the lower bound, from the law near the centroid
    obtain ⟨q, hq0, hq1, hq⟩ := exists_starStat_lt (d := -a) (by linarith)
    have hd := law_isDist hq0.le hq1
    have hp : displayCF (law q) Subtype.val = pq q := funext (displayCF_law q)
    have hF : ∀ᶠ x in 𝓝 (displayCF (law q) Subtype.val), starStat x (univ : Finset (Fin 4)) < -a := by
      rw [hp]
      exact (continuous_starStat _).continuousAt.eventually_lt continuousAt_const hq
    have hlln := tendsto_iidProb_freq (sides := (Subtype.val : BinaryGeneTree (Fin 4) → _)) hd hF
    have hcons := h q hq0 hq1
    have ev₁ := hlln.eventually_const_lt (show (3 : ℝ) / 4 < 1 by norm_num)
    have ev₂ := hcons.eventually_const_lt (show (3 : ℝ) / 4 < 1 by norm_num)
    filter_upwards [ev₁, ev₂, hβ₀, eventually_gt_atTop 0] with n h₁ h₂ hpos hn
    have hand := iidProb_and_ge' hd n (fun ω => ectoblob o (α n) (β n)
      (quartetCount Subtype.val ω) T₀ = treeOfBlobs net)
      (fun ω => starStat (fun r => quartetCount Subtype.val ω r / n) (univ : Finset (Fin 4)) < -a)
    obtain ⟨ω, hω₁, hω₂⟩ := exists_of_iidProb_pos (lt_of_lt_of_le (by linarith) hand)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set c := quartetCount (Subtype.val : BinaryGeneTree (Fin 4) → _) ω with hc
    -- the statistic is below `n (-a)`
    have hstat : starStat c (univ : Finset (Fin 4)) < n * (-a) := by
      have heq : c = fun r => (n : ℝ) * (c r / n) := by
        funext r
        field_simp
      rw [heq, starStat_const_mul hn'.ne']
      exact mul_lt_mul_of_pos_left hω₂ hn'
    -- the edge is not contracted
    have hmem : ({0, 1} : Finset (Fin 4)) ∈ afterStar o (β n) c T₀ := by
      refine treeSeq_subset_afterStar (selectedIteration o (α n) (β n) c T₀) ?_
      show _ ∈ ectoblob o (α n) (β n) c T₀
      rw [hω₁, treeOfBlobs_eq]
      exact hA
    have hle : edgeStarP o c T₀ {0, 1} ≤ β n := by
      by_contra hcon
      exact (mem_contractSides.1 hmem).2.1 (mem_filter.2 ⟨hAint, not_le.1 hcon⟩)
    -- the star p-value is at most the combined one
    have hentry : ∀ x ∈ (multipartitionQuartets T₀ {0, 1}).val.map
        (fun s => starPValue o.starTest c s.taxa), x = starPValue .lrt c univ := by
      intro x hx
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
      rw [ho, taxa_eq_univ]
    have hP : (multipartitionQuartets T₀ {0, 1}).val.map (fun s => starPValue o.starTest c s.taxa) ≠ 0 := by
      intro h'
      have : starPValue o.starTest c s₀.taxa ∈ (multipartitionQuartets T₀ {0, 1}).val.map
          (fun s => starPValue o.starTest c s.taxa) := Multiset.mem_map_of_mem _ hs₀
      simp [h'] at this
    have h01 : ∀ x ∈ (multipartitionQuartets T₀ {0, 1}).val.map
        (fun s => starPValue o.starTest c s.taxa), 0 ≤ x ∧ x ≤ 1 := by
      intro x hx
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
      exact starPValue_mem' _ (fun r => quartetCount_nonneg ω r) s.card_taxa
    have hmin := minP_le_combineP o.testCo hP h01
    rw [hentry _ (minP_mem hP fun x hx => (h01 x hx).2)] at hmin
    have hpv : Real.exp (-(n * (-a)) / 2) < β n := by
      refine lt_of_lt_of_le ?_ (hmin.trans hle)
      exact Real.exp_lt_exp.2 (by linarith)
    have hlog : -(n * (-a)) / 2 < Real.log (β n) := (Real.lt_log_iff_exp_lt hpos).2 hpv
    rw [lt_div_iff₀ hn']
    nlinarith
  · filter_upwards [hβ₀, hβ₁] with n hpos hle
    have : Real.log (β n) ≤ 0 := Real.log_nonpos hpos.le hle
    exact (div_nonpos_of_nonpos_of_nonneg this (Nat.cast_nonneg _)).trans_lt ha

end OnFour

/-- (`ecto:thm8_2_without_hpos`) **E11 of the report: Theorem 8.2 without its hypothesis on the alternatives is false for Cauchy and CBC, at all sequences.**
Suppose there were sequences `α_n`, `β_n` as in `ECToBlob.theorem8_2`, valid for every law of binary gene trees meeting both
directions of Assumption 1 at the network, with no condition on the alternatives, for all the variants with the correction `m`.
On a tree on four taxa, the laws near the centroid make the cutoff of `β_n` be `o(n)` (`OnFour.tendsto_log_beta_of_consistent`).
Then on the network `FinNetwork.Binary.net` under the law of its two displayed trees, the output is the tree `T₀` with its false
edge (`OnBinary.tendsto_lawD_self`), with probability tending to one.

The printed Cauchy formula is undefined at `p = 1`, and this is for Lean's continuous extension of it (E7). -/
theorem not_theorem8_2_without_hpos {m : TestCorrection} (hm : m = .cauchy ∨ m = .cbc) :
    ¬ ∃ α β : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, 0 < α n ∧ α n < 1) ∧ (∀ᶠ n in atTop, 0 < β n ∧ β n < 1) ∧
      ∀ {V E X : Type} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)
        (_ : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ) (_ : IsDist dist)
        (_ : Assumption1Forward N (displayCF dist Subtype.val))
        (_ : Assumption1Converse N (displayCF dist Subtype.val))
        (T₀ : Finset (Finset X)) (_ : IsResolutionOf T₀ (treeOfBlobs N))
        (o : ECToBlobOptions) (_ : o.testCo = m),
        Tendsto (fun n => iidProb dist n fun ω =>
          ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) := by
  rintro ⟨α, β, -, hβ, hαp, hβp, h⟩
  let o : ECToBlobOptions := ⟨.bi, m, .early, .lrt⟩
  have hβpos : ∀ᶠ n in atTop, 0 < β n := hβp.mono fun _ hn => hn.1
  have hlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) :=
    OnFour.tendsto_log_beta_of_consistent (α := α) hβpos (hβp.mono fun _ hn => hn.2.le)
      (o := o) rfl fun q hq0 hq1 => by
        obtain ⟨h₁, h₂⟩ := OnFour.law_assumption1 hq1
        exact h OnFour.net OnFour.net_isPhylogenetic (OnFour.law q) (OnFour.law_isDist hq0.le hq1) h₁ h₂
          OnFour.T₀ ⟨OnFour.T₀_isUnrootedTree, OnFour.treeOfBlobs_eq.le⟩ o rfl
  have hβ₀ : Tendsto β atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hβ, hβpos⟩
  have hself := OnBinary.tendsto_lawD_self (o := o) hm (α := α) (hαp.mono fun _ hn => hn.2.le) hβ₀ hlog
  obtain ⟨h₁, h₂⟩ := OnBinary.lawD_assumption1
  have hne : FinNetwork.Binary.T₀ ≠ treeOfBlobs FinNetwork.Binary.net := fun he =>
    FinNetwork.Binary.T₀_ne_treeOfBlobs.2 (he ▸ FinNetwork.Binary.T₀_ne_treeOfBlobs.1)
  have hzero := tendsto_eq_zero_of_tendsto_eq OnBinary.lawD_isDist hne hself
  have hone := h FinNetwork.Binary.net FinNetwork.Binary.net_isPhylogenetic OnBinary.lawD
    OnBinary.lawD_isDist h₁ h₂ FinNetwork.Binary.T₀ FinNetwork.Binary.T₀_isResolution o rfl
  exact one_ne_zero (tendsto_nhds_unique hone hzero)

/-! ### Combining the edge p-values under CBC -/

namespace OnBinary

open FinNetwork.Binary

/-- The clusters of the gene trees of `lawC`: `((d,e),(a,(b,c)))`, `((a,d),(c,(b,e)))` and `((a,e),(c,(b,d)))`. -/
def hierC : Fin 3 → Finset (Finset (Fin 5)) :=
  ![clusters {3, 4} {1, 2} {0, 1, 2}, clusters {0, 3} {1, 4} {1, 2, 4}, clusters {0, 4} {1, 3} {1, 2, 3}]

/-- The three gene trees. -/
def geneC (i : Fin 3) : BinaryGeneTree (Fin 5) :=
  ⟨unroot (hierC i), hierC i, by unfold IsHierarchy; revert i; decide, rfl, by revert i; decide⟩

/-- The weights, in fourths. -/
def wtC : Fin 3 → ℕ := ![2, 1, 1]

/-- **The law with weights `1/2`, `1/4`, `1/4`.** The cut quartets have concordance factors `(1/2, 1/4, 1/4)`, and the three of them
are decided by the same gene tree on each sample. -/
def lawC : BinaryGeneTree (Fin 5) → ℝ := pointLaw geneC fun i => (wtC i : ℝ) / 4

theorem lawC_isDist : IsDist lawC :=
  pointLaw_isDist (fun _ => by positivity) (by
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have : ∑ i, wtC i = 4 := by decide
    rw [this]
    norm_num)

/-- The gene tree `i` displays the quartet tree with cherries `B`, `C`. -/
def dspC (i : Fin 3) (B C : Finset (Fin 5)) : Prop :=
  ∃ A ∈ unroot (hierC i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C

instance (i : Fin 3) (B C : Finset (Fin 5)) : Decidable (dspC i B C) :=
  inferInstanceAs (Decidable (∃ A ∈ unroot (hierC i), A ∩ (B ∪ C) = B ∨ A ∩ (B ∪ C) = C))

/-- The weight of the gene trees displaying the quartet tree with cherries `B`, `C`. -/
def countC (B C : Finset (Fin 5)) : ℕ := ∑ i, wtC i * if dspC i B C then 1 else 0

theorem countC_eq : ∀ B ∈ powersetCard 2 (univ : Finset (Fin 5)),
    ∀ C ∈ powersetCard 2 (univ : Finset (Fin 5)), Disjoint B C →
      countC B C = if B = {3, 4} ∨ C = {3, 4} then 2 else if ({3, 4} : Finset (Fin 5)) ⊆ B ∪ C then 1
        else if B = {1, 2} ∨ C = {1, 2} then 3 else if B = {0, 2} ∨ C = {0, 2} then 1 else 0 := by
  decide

/-- The concordance factors of `lawC`. -/
theorem displayCF_lawC (s : QuartetTree (Fin 5)) :
    displayCF lawC Subtype.val s = if ({3, 4} : Finset (Fin 5)) ∈ s.val then 1 / 2
      else if ({3, 4} : Finset (Fin 5)) ⊆ s.taxa then 1 / 4
      else if ({1, 2} : Finset (Fin 5)) ∈ s.val then 3 / 4
      else if ({0, 2} : Finset (Fin 5)) ∈ s.val then 1 / 4 else 0 := by
  obtain ⟨B, C, hs, hB, hC, hd, ht⟩ := s.exists_eq_pair
  have hsum : displayCF lawC Subtype.val s = (countC B C : ℝ) / 4 := by
    unfold lawC
    rw [displayCF_pointLaw]
    unfold countC
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : Displays (geneC i).1 s ↔ dspC i B C := displays_iff_of_val hs ht
    simp only [h]
    split_ifs <;> simp
  have hc := countC_eq B (mem_powersetCard.2 ⟨subset_univ _, hB⟩) C
    (mem_powersetCard.2 ⟨subset_univ _, hC⟩) hd
  have hmem : ∀ P : Finset (Fin 5), P ∈ s.val ↔ B = P ∨ C = P := by
    intro P
    rw [hs]
    simp only [mem_insert, mem_singleton]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  rw [hsum, hc, ht]
  simp only [hmem]
  split_ifs <;> norm_num

theorem lawC_assumption1 :
    Assumption1Forward net (displayCF lawC Subtype.val) ∧
      Assumption1Converse net (displayCF lawC Subtype.val) := by
  refine assumption1_of_shape (A := 1 / 2) (B := 1 / 4) (C := 3 / 4) (D := 1 / 4) (by norm_num)
    (by norm_num) (by norm_num) (fun s h => ?_) (fun s h h' => ?_) (fun s h h' => ?_)
    (fun s h h' => ?_) (fun s h h' => ?_)
  · rw [displayCF_lawC, ite_eq_left h]
  · rw [displayCF_lawC, ite_eq_right h, ite_eq_left h']
  · have hn : ({3, 4} : Finset (Fin 5)) ∉ s.val := fun h₃ => h' (s.subset_taxa h₃)
    rw [displayCF_lawC, ite_eq_right hn, ite_eq_right h', ite_eq_left h]
  · have hn : ({3, 4} : Finset (Fin 5)) ∉ s.val := fun h₃ => h' (s.subset_taxa h₃)
    have hn' : ({1, 2} : Finset (Fin 5)) ∉ s.val := fun h₃ => by
      have := s.2.2.2 _ h₃ _ h (by decide)
      exact absurd this (by decide)
    rw [displayCF_lawC, ite_eq_right hn, ite_eq_right h', ite_eq_right hn', ite_eq_left h]
  · have hn : ({3, 4} : Finset (Fin 5)) ∉ s.val := fun h₃ => h' (s.subset_taxa h₃)
    have hn' : ({1, 2} : Finset (Fin 5)) ∉ s.val := fun h₃ => by
      have := s.2.2.2 _ h₃ _ h (by decide)
      exact absurd this (by decide)
    have hn'' : ({0, 2} : Finset (Fin 5)) ∉ s.val := fun h₃ => by
      have := s.2.2.2 _ h₃ _ h (by decide)
      exact absurd this (by decide)
    rw [displayCF_lawC, ite_eq_right hn, ite_eq_right h', ite_eq_right hn', ite_eq_right hn'']

/-- Its alternatives on T1-strict quartets have positive probability, so it meets the hypothesis of `ECToBlob.theorem8_2`. -/
theorem lawC_hpos (s : QuartetTree (Fin 5)) (hs : IsT1Strict (displayCF lawC Subtype.val) s)
    (r : QuartetTree (Fin 5)) (hr : r ∈ s.alternatives) : 0 < displayCF lawC Subtype.val r := by
  obtain ⟨_, h₂⟩ := lawC_assumption1
  have hcut : InducedCutSplit net s := by
    by_contra hcon
    exact h₂.t1 s hcon hs
  have h₀ := mem_val_of_inducedCutSplit hcut
  obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
  rw [displayCF_lawC, ite_eq_right (fun h => hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt h h₀)),
    ite_eq_left (hrt ▸ s.subset_taxa h₀)]
  norm_num

/-! #### The quartets of the cut edge have equal p-values -/

variable {n : ℕ} {ω : Fin n → BinaryGeneTree (Fin 5)}

/-- The number of draws equal to the gene tree `j`. -/
def numC (ω : Fin n → BinaryGeneTree (Fin 5)) (j : Fin 3) : ℝ :=
  ((univ.filter fun i => ω i = geneC j).card : ℝ)

/-- On a sample of positive probability, a quartet tree displayed by the gene tree `j₀` alone has the count of `j₀`. -/
theorem quartetCount_eq_numC (hω : ∀ i, lawC (ω i) ≠ 0) {a b c d : Fin 5}
    (hc : ({a, b, c, d} : Finset (Fin 5)).card = 4) {j₀ : Fin 3}
    (hj : ∀ j, dspC j {a, b} {c, d} ↔ j = j₀) :
    quartetCount Subtype.val ω (quartetTree a b c d hc) = numC ω j₀ := by
  have ht : (quartetTree a b c d hc).taxa = {a, b} ∪ {c, d} := by
    rw [taxa_quartetTree]
    ext x
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have hdisp : ∀ j, Displays (geneC j).1 (quartetTree a b c d hc) ↔ j = j₀ := fun j =>
    (displays_iff_of_val (quartetTree_val a b c d hc) ht).trans (hj j)
  unfold quartetCount numC
  congr 2
  ext i
  simp only [mem_filter, mem_univ, true_and]
  obtain ⟨j, hj', -⟩ := exists_gene_of_ne_zero (hω i)
  rw [hj', hdisp j]
  constructor
  · rintro rfl
    rfl
  · intro h
    have hj₀ := (hdisp j₀).2 rfl
    rw [← h] at hj₀
    exact (hdisp j).1 hj₀

/-- The alternatives of a quartet tree on `Fin 5`, from two others on the same taxa. -/
theorem alternatives_eq {s r₁ r₂ : QuartetTree (Fin 5)} (h₁ : r₁.taxa = s.taxa) (h₂ : r₂.taxa = s.taxa)
    (hne₁ : r₁ ≠ s) (hne₂ : r₂ ≠ s) (hne : r₁ ≠ r₂) : s.alternatives = {r₁, r₂} := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact QuartetTree.mem_alternatives.2 ⟨h₁, hne₁⟩
    · exact QuartetTree.mem_alternatives.2 ⟨h₂, hne₂⟩
  · rw [s.card_alternatives, Finset.card_pair hne]

/-- The p-value of `de|yz`, on a sample of positive probability, from the counts of the three gene trees. -/
theorem t1PValue_de (hω : ∀ i, lawC (ω i) ≠ 0) {y z : Fin 5}
    (hc : ({3, 4, y, z} : Finset (Fin 5)).card = 4) (hc₁ : ({3, y, 4, z} : Finset (Fin 5)).card = 4)
    (hc₂ : ({3, z, 4, y} : Finset (Fin 5)).card = 4) {j₁ j₂ : Fin 3}
    (hj : ({j₁, j₂} : Finset (Fin 3)) = {1, 2}) (hne' : j₁ ≠ j₂)
    (h₀ : ∀ j, dspC j {3, 4} {y, z} ↔ j = 0) (h₁ : ∀ j, dspC j {3, y} {4, z} ↔ j = j₁)
    (h₂ : ∀ j, dspC j {3, z} {4, y} ↔ j = j₂) :
    t1PValue (quartetCount Subtype.val ω) (quartetTree 3 4 y z hc) =
      Trinomial.t1PValueR (numC ω 0) (numC ω 1) (numC ω 2) := by
  have hyz : y ≠ z := (ne_of_card_four hc).2.2.2.2.2
  have ht₁ : (quartetTree 3 y 4 z hc₁).taxa = (quartetTree 3 4 y z hc).taxa := by
    rw [taxa_quartetTree, taxa_quartetTree]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  have ht₂ : (quartetTree 3 z 4 y hc₂).taxa = (quartetTree 3 4 y z hc).taxa := by
    rw [taxa_quartetTree, taxa_quartetTree]
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  obtain ⟨_, h3y, h3z, h4y, h4z, _⟩ := ne_of_card_four hc
  have hfact₁ : ∀ y z : Fin 5, y ≠ 3 → y ≠ 4 → z ≠ 3 → z ≠ 4 →
      ¬ (({3, 4} : Finset (Fin 5)) = {3, y} ∨ ({3, 4} : Finset (Fin 5)) = {4, z}) := by decide
  have hfact₂ : ∀ y z : Fin 5, y ≠ z → y ≠ 3 → y ≠ 4 → z ≠ 3 → z ≠ 4 →
      ¬ (({3, y} : Finset (Fin 5)) = {3, z} ∨ ({3, y} : Finset (Fin 5)) = {4, y}) := by decide
  have hne₁ : quartetTree 3 y 4 z hc₁ ≠ quartetTree 3 4 y z hc := by
    intro h
    have hm : ({3, 4} : Finset (Fin 5)) ∈ (quartetTree 3 y 4 z hc₁).val := by rw [h]; simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    exact hfact₁ y z h3y.symm h4y.symm h3z.symm h4z.symm hm
  have hne₂ : quartetTree 3 z 4 y hc₂ ≠ quartetTree 3 4 y z hc := by
    intro h
    have hm : ({3, 4} : Finset (Fin 5)) ∈ (quartetTree 3 z 4 y hc₂).val := by rw [h]; simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    exact hfact₁ z y h3z.symm h4z.symm h3y.symm h4y.symm hm
  have hne : quartetTree 3 y 4 z hc₁ ≠ quartetTree 3 z 4 y hc₂ := by
    intro h
    have hm : ({3, y} : Finset (Fin 5)) ∈ (quartetTree 3 z 4 y hc₂).val := by rw [← h]; simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    exact hfact₂ y z hyz h3y.symm h4y.symm h3z.symm h4z.symm hm
  rw [t1PValue_eq_t1PValueR _ hne (alternatives_eq ht₁ ht₂ hne₁ hne₂ hne),
    quartetCount_eq_numC hω hc h₀, quartetCount_eq_numC hω hc₁ h₁, quartetCount_eq_numC hω hc₂ h₂]
  have hcases : ∀ j₁ j₂ : Fin 3, ({j₁, j₂} : Finset (Fin 3)) = {1, 2} → j₁ ≠ j₂ →
      (j₁ = 1 ∧ j₂ = 2) ∨ (j₁ = 2 ∧ j₂ = 1) := by decide
  rcases hcases j₁ j₂ hj hne' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact t1PValueR_swap _ _ _

/-- The three quartet trees of the cut edge have the same p-value on each sample of positive probability. -/
theorem t1PValue_of_mem_bipartition (hω : ∀ i, lawC (ω i) ≠ 0) {s : QuartetTree (Fin 5)}
    (hs : s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5))) :
    t1PValue (quartetCount Subtype.val ω) s = Trinomial.t1PValueR (numC ω 0) (numC ω 1) (numC ω 2) := by
  have h₀ := mem_val_of_mem_bipartition hs
  obtain ⟨B, C, hsv, hB, hC, hd, _⟩ := s.exists_eq_pair
  have hpair : s.val = {{3, 4}, if B = {3, 4} then C else B} := by
    rw [hsv] at h₀ ⊢
    simp only [mem_insert, mem_singleton] at h₀
    rcases h₀ with h | h
    · subst h
      simp
    · subst h
      by_cases hBC : B = {3, 4}
      · subst hBC
        exact absurd hd (by decide)
      · rw [ite_eq_right hBC, Finset.pair_comm]
  set D := if B = {3, 4} then C else B with hD
  have hDcard : D.card = 2 := by
    rw [hD]
    split_ifs <;> assumption
  have hDdisj : Disjoint ({3, 4} : Finset (Fin 5)) D := by
    have := s.2.2.2 {3, 4} (by rw [hpair]; simp) D (by rw [hpair]; simp) (by
      intro h
      rw [← h] at hDcard
      have hc₂ := s.2.1
      rw [hpair, ← h] at hc₂
      simp at hc₂)
    exact this
  have hdec : ∀ D : Finset (Fin 5), D.card = 2 → Disjoint ({3, 4} : Finset (Fin 5)) D →
      D = {0, 1} ∨ D = {0, 2} ∨ D = {1, 2} := by decide
  rcases hdec D hDcard hDdisj with h | h | h
  · have hc : ({3, 4, 0, 1} : Finset (Fin 5)).card = 4 := by decide
    have hse : s = quartetTree 3 4 0 1 hc := Subtype.ext (by rw [hpair, h]; rfl)
    rw [hse]
    exact t1PValue_de hω hc (by decide) (by decide) (j₁ := 1) (j₂ := 2) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · have hc : ({3, 4, 0, 2} : Finset (Fin 5)).card = 4 := by decide
    have hse : s = quartetTree 3 4 0 2 hc := Subtype.ext (by rw [hpair, h]; rfl)
    rw [hse]
    exact t1PValue_de hω hc (by decide) (by decide) (j₁ := 1) (j₂ := 2) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · have hc : ({3, 4, 1, 2} : Finset (Fin 5)).card = 4 := by decide
    have hse : s = quartetTree 3 4 1 2 hc := Subtype.ext (by rw [hpair, h]; rfl)
    rw [hse]
    exact t1PValue_de hω hc (by decide) (by decide) (j₁ := 2) (j₂ := 1) (by decide)
      (by decide) (by decide) (by decide) (by decide)

/-! #### The false edge stays -/

/-- On a sample of positive probability with the common p-value of the cut edge above `1/2`, and on which Step 3 keeps `T₀`, the
variant with the CBC combination of the edge p-values returns `T₀`: the edge `de` has p-value `1`, from Bonferroni, so every tree
with it has overall p-value `1`. -/
theorem ectoblobEdge_eq_self {o : ECToBlobOptions} (hm : o.testCo = .cbc) {α β : ℝ} (hα : α ≤ 1)
    (hω : ∀ i, lawC (ω i) ≠ 0)
    (hp : 1 / 2 < Trinomial.t1PValueR (numC ω 0) (numC ω 1) (numC ω 2))
    (hafter : afterStar o β (quartetCount Subtype.val ω) T₀ = T₀) :
    ectoblobEdge o α β (quartetCount Subtype.val ω) T₀ = T₀ := by
  unfold ectoblobEdge
  rw [hafter]
  set c := quartetCount (Subtype.val : BinaryGeneTree (Fin 5) → _) ω with hc
  set P := Trinomial.t1PValueR (numC ω 0) (numC ω 1) (numC ω 2) with hP
  have hf : ∀ s, 0 < t1PValue c s ∧ t1PValue c s ≤ 1 := fun _ =>
    ⟨t1PValue_pos _ _, Trinomial.t1Tail_le_one _ _⟩
  have hmem : ∀ (Q : Finset (QuartetTree (Fin 5))), ∀ x ∈ Q.val.map (t1PValue c), 0 < x ∧ x ≤ 1 := by
    intro Q x hx
    obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hx
    exact hf s
  -- two quartets of the cut edge
  have hc₁ : ({3, 4, 0, 1} : Finset (Fin 5)).card = 4 := by decide
  have hc₂ : ({3, 4, 0, 2} : Finset (Fin 5)).card = 4 := by decide
  have hS₁ : quartetTree 3 4 0 1 hc₁ ∈ multipartitionQuartets T₀ ({3, 4} : Finset (Fin 5)) := by
    refine quartetTree_mem hc₁ (by decide) (by decide) (by decide) (by decide) ?_ ?_
    · unfold FalseEdge.Sep T₀ H₀ unroot
      decide
    · unfold FalseEdge.Sep T₀ H₀ unroot
      decide
  have hS₂ : quartetTree 3 4 0 2 hc₂ ∈ multipartitionQuartets T₀ ({3, 4} : Finset (Fin 5)) := by
    refine quartetTree_mem hc₂ (by decide) (by decide) (by decide) (by decide) ?_ ?_
    · unfold FalseEdge.Sep T₀ H₀ unroot
      decide
    · unfold FalseEdge.Sep T₀ H₀ unroot
      decide
  have hS₁₂ : quartetTree 3 4 0 1 hc₁ ≠ quartetTree 3 4 0 2 hc₂ := by
    intro h
    have := congrArg Subtype.val h
    simp only [quartetTree_val] at this
    exact absurd this (by decide)
  -- the value of the edge
  have hedge : ∀ {T : Finset (Finset (Fin 5))}, T ⊆ T₀ → ∀ {B : Finset (Fin 5)},
      multipartitionQuartets T₀ B = multipartitionQuartets T₀ {3, 4} →
      (∀ s, B ∩ s.taxa ∈ s.val → s ∈ bipartitionQuartets ({3, 4} : Finset (Fin 5))) →
      edgeT1P o c T₀ T B = 1 := by
    intro T hT B hBm hBb
    unfold edgeT1P
    rw [hm]
    have hQ₁ : quartetTree 3 4 0 1 hc₁ ∈ edgeQuartets o T₀ T B :=
      multipartitionQuartets_subset_edgeQuartets hT B (hBm ▸ hS₁)
    have hQ₂ : quartetTree 3 4 0 2 hc₂ ∈ edgeQuartets o T₀ T B :=
      multipartitionQuartets_subset_edgeQuartets hT B (hBm ▸ hS₂)
    have hcard : 2 ≤ (edgeQuartets o T₀ T B).card :=
      Finset.one_lt_card.2 ⟨_, hQ₁, _, hQ₂, hS₁₂⟩
    have hval : ∀ x ∈ (edgeQuartets o T₀ T B).val.map (fun s => t1PValue c s), x = P := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hx
      exact t1PValue_of_mem_bipartition hω (hBb s (mem_of_mem_edgeQuartets hs))
    have hne : (edgeQuartets o T₀ T B).val.map (fun s => t1PValue c s) ≠ 0 := by
      intro h'
      have : t1PValue c (quartetTree 3 4 0 1 hc₁) ∈
          (edgeQuartets o T₀ T B).val.map (fun s => t1PValue c s) := Multiset.mem_map_of_mem _ hQ₁
      simp [h'] at this
    refine combineP_cbc_eq_one_of_bon hne (hmem _) ?_
    rw [hval _ (minP_mem hne fun x hx => (hmem _ x hx).2), Multiset.card_map]
    have h₂ : (2 : ℝ) ≤ ((edgeQuartets o T₀ T B).val.card : ℝ) := by exact_mod_cast hcard
    nlinarith
  have hA : ∀ {T : Finset (Finset (Fin 5))}, T ⊆ T₀ → edgeT1P o c T₀ T {3, 4} = 1 := fun hT =>
    hedge hT rfl fun s hs => mem_filter.2 ⟨mem_univ _, hs⟩
  have hAc : ∀ {T : Finset (Finset (Fin 5))}, T ⊆ T₀ → edgeT1P o c T₀ T ({3, 4} : Finset (Fin 5))ᶜ = 1 :=
    fun hT => hedge hT (multipartitionQuartets_compl _ _) fun s hs => mem_filter.2
      ⟨mem_univ _, by simpa using compl_inter_taxa_mem hs⟩
  have hAT₀ : ({3, 4} : Finset (Fin 5)) ∈ T₀ := T₀_internal_de
  have hAcT₀ : ({3, 4} : Finset (Fin 5))ᶜ ∈ T₀ := IsUnrootedTree.compl_mem T₀_isUnrootedTree hAT₀
  have hle : ∀ T ⊆ T₀, ∀ B ∈ internalSides T, edgeT1P o c T₀ T B ≤ 1 := fun T _ B _ =>
    (Remarks.combineP_mem _ fun x hx => ⟨(hmem _ x hx).1.le, (hmem _ x hx).2⟩).2
  refine outputBy_eq_self_of_forall_le o.rule fun i => ?_
  rcases mem_seqBy_or (edgeP := edgeT1P o c T₀) (T₁ := T₀) hAT₀ hAcT₀
      (fun T hT _ _ => ⟨hA hT, hAc hT⟩) hle i with h | h
  · -- a tree with the edge
    have hint : ({3, 4} : Finset (Fin 5)) ∈ internalSides (seqBy (edgeT1P o c T₀) T₀ i) :=
      mem_internalSides.2 ⟨h.1, by decide⟩
    have hval : treeEdgeP o c T₀ (seqBy (edgeT1P o c T₀) T₀ i) = 1 := by
      unfold treeEdgeP
      rw [hm]
      refine combineP_cbc_eq_one ?_ fun x hx => ?_
      · exact Multiset.mem_map.2 ⟨_, hint, hA (seqBy_subset i)⟩
      · obtain ⟨B, _, rfl⟩ := Multiset.mem_map.1 hx
        refine ⟨combineP_pos _ (hmem _), (Remarks.combineP_mem _ fun x hx =>
          ⟨(hmem _ x hx).1.le, (hmem _ x hx).2⟩).2⟩
    rw [hval]
    exact hα
  · -- a tree with no internal edge
    unfold treeEdgeP combineP
    rw [h]
    simpa using hα

/-- The p-value of `de|ab` is asymptotically uniform. -/
theorem tendsto_prob_gt_half :
    Tendsto (fun n => iidProb lawC n fun ω =>
      1 / 2 < t1PValue (quartetCount Subtype.val ω) (quartetTree 3 4 0 1 (by decide)))
      atTop (𝓝 (1 / 2)) := by
  have hd := lawC_isDist
  have hone := displaysOne_binaryGeneTree lawC
  obtain ⟨h₁, _⟩ := lawC_assumption1
  have hc : ({3, 4, 0, 1} : Finset (Fin 5)).card = 4 := by decide
  have hstrict := h₁.t1 (quartetTree 3 4 0 1 hc) (inducedCutSplit_of_mem_val (by simp))
  have hU := t1PValue_asymptoticallyUniform hd hone hstrict.1 hstrict.2
    (lawC_hpos _ hstrict) (1 / 2) (by norm_num) (by norm_num)
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hU
  norm_num at hlim
  refine hlim.congr fun n => ?_
  rw [← iidProb_not hd]
  simp only [not_le]

/-- (`ecto:sec10_cbc_edges`) **ECToBlob §10: combining the edge p-values under CBC fails.** On the network `FinNetwork.Binary.net` with the law `lawC`, which
meets both directions of Assumption 1 and has positive alternatives, the variant in which the overall p-value combines the edge
p-values, with CBC, outputs the tree `T₀` with its false edge with probability at least `1/2 - ε`, for large `n`. So it is not
consistent, at any levels `α_n ≤ 1`, `β_n → 0` from above with `o(n)` cutoffs. The other three variants are consistent there. -/
theorem not_consistency_edge_combination_cbc :
    IsDist lawC ∧ Assumption1Forward net (displayCF lawC Subtype.val) ∧
      Assumption1Converse net (displayCF lawC Subtype.val) ∧
      (∀ s, IsT1Strict (displayCF lawC Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF lawC Subtype.val r) ∧
      (∀ o : ECToBlobOptions, o.testCo ≠ .cbc → Tendsto (fun n => iidProb lawC n fun ω =>
        ectoblobEdge o (alphaSeq n) (betaSeq n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs net)
        atTop (𝓝 1)) ∧
      ∀ o : ECToBlobOptions, o.testCo = .cbc → ∀ {α β : ℕ → ℝ}, (∀ᶠ n in atTop, α n ≤ 1) →
        Tendsto β atTop (𝓝[>] 0) → Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0) →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, 1 / 2 - ε < iidProb lawC n fun ω =>
          ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) T₀ = T₀) ∧
        ¬ Tendsto (fun n => iidProb lawC n fun ω =>
          ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs net) atTop (𝓝 1) := by
  have hd := lawC_isDist
  obtain ⟨h₁, h₂⟩ := lawC_assumption1
  refine ⟨hd, h₁, h₂, lawC_hpos, fun o hm => ?_, fun o hm {α β} hα hβ₀ hβ => ?_⟩
  · exact consistency_edge_combination net net_isPhylogenetic lawC hd h₁ h₂ T₀ T₀_isResolution o hm
      fun _ s hs r hr => lawC_hpos s hs r hr
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, 1 / 2 - ε < iidProb lawC n fun ω =>
      ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) T₀ = T₀ := by
    intro ε hε
    have hstar := eventually_afterStar_eq_binary hd o T₀_isUnrootedTree
      (fun B _ s _ hu => not_hasTrivialFourBlob s.card_taxa ((uniform_iff h₁ h₂ s).1 hu)) hβ₀ hβ
      (half_pos hε)
    have hgt := tendsto_prob_gt_half.eventually_const_lt (show 1 / 2 - ε / 2 < 1 / 2 by linarith)
    filter_upwards [hstar, hgt, hα] with n h₁' h₂' hαn
    have hforall := iidProb_forall_ne_zero hd n
    have hand := iidProb_and_ge' hd n
      (fun ω => afterStar o (β n) (quartetCount Subtype.val ω) T₀ = T₀ ∧
        1 / 2 < t1PValue (quartetCount Subtype.val ω) (quartetTree 3 4 0 1 (by decide)))
      (fun ω => ∀ i, lawC (ω i) ≠ 0)
    have hand' := iidProb_and_ge' hd n (fun ω => afterStar o (β n) (quartetCount Subtype.val ω) T₀ = T₀)
      (fun ω => 1 / 2 < t1PValue (quartetCount Subtype.val ω) (quartetTree 3 4 0 1 (by decide)))
    rw [hforall] at hand
    have hgoal' : 1 / 2 - ε < iidProb lawC n fun ω =>
        (afterStar o (β n) (quartetCount Subtype.val ω) T₀ = T₀ ∧
          1 / 2 < t1PValue (quartetCount Subtype.val ω) (quartetTree 3 4 0 1 (by decide))) ∧
        ∀ i, lawC (ω i) ≠ 0 := by linarith
    refine hgoal'.trans_le (iidProb_mono hd fun ω hω => ?_)
    obtain ⟨⟨hafter, hgt'⟩, hpos⟩ := hω
    refine ectoblobEdge_eq_self hm hαn hpos ?_ hafter
    rwa [t1PValue_of_mem_bipartition hpos (mem_filter.2 ⟨mem_univ _, by
      rw [taxa_quartetTree]
      decide⟩)] at hgt'
  refine ⟨key, fun hcon => ?_⟩
  have hne : T₀ ≠ treeOfBlobs net := fun he => T₀_ne_treeOfBlobs.2 (he ▸ T₀_ne_treeOfBlobs.1)
  have ev₁ := key (1 / 4) (by norm_num)
  have ev₂ := hcon.eventually_const_lt (show (7 : ℝ) / 8 < 1 by norm_num)
  obtain ⟨n, hn₁, hn₂⟩ := (ev₁.and ev₂).exists
  have hle := iidProb_mono hd (n := n)
    (Ev := fun ω => ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) T₀ = T₀)
    (Ev' := fun ω => ¬ ectoblobEdge o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs net)
    (fun ω h₃ h₄ => hne (h₃.symm.trans h₄))
  rw [iidProb_not hd] at hle
  norm_num at hn₁
  linarith

end OnBinary

end ECToBlob.BinaryLaw
