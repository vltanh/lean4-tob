module

public import ECToBlob.Remark84

/-!
# ECToBlob §10: other data types and other tests

"While we have focused here on using qcCFs to test the topology of each 4-taxon set, our framework could easily be
extended to other data types and statistical tests, since at its core ECToBlob takes quartet p-values as input. The input
star test p-values could come from any valid test of a multifurcation, and the input T1 test p-values from any test that
the 4-taxon subnetwork has the desired edge split." (the paper's text, lines 1419-1423.)

Here the algorithm takes two tables of quartet p-values, `g` for the star test and `f` for the T1 test (`afterStarBy`,
`ectoblobBy`). What the proof of Theorem 8.2 needs of these is `AdequateTests`, at levels `α_n`, `β_n`:

* the p-values are in `[0, 1]`;
* under the null, each is bounded below in probability, and for `cauchy` and `cbc` also bounded away from `1`;
* under the alternative, each is below any constant times the level, with probability tending to one.

So "valid" in the sentence is not enough as it stands: the test needs power at the level `α_n`, and for `cauchy` and `cbc`
it needs p-values away from `1` under the null, which a conservative test does not have
(`ECToBlob.DisplayedTree.ectoblob_eq_afterStar`). Then `tendsto_ectoblobBy_limitTree` and `consistency_ectoblobBy` are
the conclusion of Theorem 8.2, and of its form on an arbitrary tree `T₀`. The proof is the one of Theorem 8.2, test by
test, and its end is `Coarsening.IsLimit.outputBy_eq`.

`theorem8_2_levels` is Theorem 8.2 itself at any levels with `α_n, β_n → 0` and `o(n)` cutoffs, which is lines 1159-1167,
and includes `β_n = 1/n`, the choice of the BIC at line 1162.

The instances: `ECToBlob.DisplayedTree` (the displayed tree model), `ECToBlob.SumOfPairs` (distances).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.QuartetTests Finset Filter Topology
open scoped Classical

namespace ECToBlob.Framework

open ECToBlob.Deterministic ECToBlob.Coarsening

section Deterministic

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

/-- Step 3 of the algorithm, for star p-values `g` of the quartets: the combined star p-value of the edge with side `A`. -/
def edgeStarBy (o : ECToBlobOptions) (g : QuartetTree X → ℝ) (T₀ : Finset (Finset X)) (A : Finset X) : ℝ :=
  combineP o.testCo ((multipartitionQuartets T₀ A).val.map g)

/-- Step 3 of the algorithm, for star p-values `g` of the quartets. -/
def afterStarBy (o : ECToBlobOptions) (β : ℝ) (g : QuartetTree X → ℝ) (T₀ : Finset (Finset X)) :
    Finset (Finset X) :=
  contractSides T₀ ((internalSides T₀).filter fun A => β < edgeStarBy o g T₀ A)

/-- **The algorithm on quartet p-values**: `g` for the star test, `f` for the T1 test. -/
def ectoblobBy (o : ECToBlobOptions) (α β : ℝ) (g f : QuartetTree X → ℝ) (T₀ : Finset (Finset X)) :
    Finset (Finset X) :=
  outputBy o.rule α (edgeTestP o f T₀) (treeTestP o f) (afterStarBy o β g T₀)

/-- The algorithm of the paper is this one, on the p-values of its tests. -/
theorem ectoblob_eq_ectoblobBy (o : ECToBlobOptions) (α β : ℝ) (c : QuartetTree X → ℝ)
    (T₀ : Finset (Finset X)) :
    ectoblob o α β c T₀ =
      ectoblobBy o α β (fun s => starPValue o.starTest c s.taxa) (t1PValue c) T₀ := rfl

theorem afterStarBy_subset {o : ECToBlobOptions} {β : ℝ} {g : QuartetTree X → ℝ}
    {T₀ : Finset (Finset X)} : afterStarBy o β g T₀ ⊆ T₀ := Finset.filter_subset _ _

/-- A run on tables of p-values on which every test comes out right. -/
structure RunBy (N : RootedNetwork V E X) (g f : QuartetTree X → ℝ) (T₀ : Finset (Finset X))
    (o : ECToBlobOptions) (α β : ℝ) : Prop where
  phylo : N.IsPhylogenetic
  isTree : IsUnrootedTree T₀
  star : ∀ A ∈ internalSides T₀, TestCorrect (fun s => HasTrivialFourBlob N s.taxa)
    (multipartitionQuartets T₀ A) β (edgeStarBy o g T₀ A)
  edge : ∀ T ⊆ T₀, ∀ A ∈ internalSides T, TestCorrect (IsNullQuartet N) (edgeQuartets o T₀ T A) α
    (edgeTestP o f T₀ T A)
  tree : ∀ T ⊆ T₀, TestCorrect (IsNullQuartet N) (univ.filter fun s => Displays T s) α
    (treeTestP o f T)

variable {g f : QuartetTree X → ℝ} {T₀ : Finset (Finset X)} {o : ECToBlobOptions} {α β : ℝ}

theorem RunBy.limitTree_subset_afterStarBy (R : RunBy N g f T₀ o α β) :
    limitTree N T₀ ⊆ afterStarBy o β g T₀ := by
  have key : ∀ A ∈ limitTree N T₀,
      A ∉ (internalSides T₀).filter fun A => β < edgeStarBy o g T₀ A := by
    intro A hA hmem
    obtain ⟨hint, hβ⟩ := mem_filter.1 hmem
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hint
    rcases (mem_limitTree.1 hA).2 with h | ⟨⟨s, hs, hn⟩, _⟩
    · exact h h₂
    · exact absurd hβ (not_lt_of_gt ((R.star A hint).2 ⟨s, hs, hn⟩))
  intro A hA
  exact mem_contractSides.2 ⟨limitTree_subset T₀ hA, key A hA, key _ (compl_mem_limitTree R.isTree hA)⟩

theorem RunBy.exists_not_null_bipartition (R : RunBy N g f T₀ o α β) {A : Finset X}
    (hA : A ∈ afterStarBy o β g T₀) (h₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card) (hAL : A ∉ limitTree N T₀) :
    ∃ s ∈ bipartitionQuartets A, ¬ IsNullQuartet N s := by
  obtain ⟨hAT₀, hnot, _⟩ := mem_contractSides.1 hA
  have hint : A ∈ internalSides T₀ := mem_internalSides.2 ⟨hAT₀, h₂⟩
  by_contra hcon
  push Not at hcon
  refine hAL (mem_limitTree.2 ⟨hAT₀, Or.inr ⟨?_, hcon⟩⟩)
  by_contra hall
  push Not at hall
  exact hnot (mem_filter.2 ⟨hint, (R.star A hint).1 fun s hs => hall s hs⟩)

theorem RunBy.exists_not_null_edgeQuartets (R : RunBy N g f T₀ o α β)
    {T : Finset (Finset X)} (hT : T ⊆ T₀) {A : Finset X} (hA : A ∈ afterStarBy o β g T₀)
    (h₂ : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card) (hAL : A ∉ limitTree N T₀) :
    ∃ s ∈ edgeQuartets o T₀ T A, ¬ IsNullQuartet N s := by
  obtain ⟨s₀, hs₀, hn₀⟩ := R.exists_not_null_bipartition hA h₂ hAL
  by_contra hcon
  push Not at hcon
  refine hn₀ (forall_bipartition_of_forall_multipartition R.phylo
    (isSplitFamily_of_internal R.isTree h₂.1) h₂.1 h₂.2 (fun s hs => ?_) s₀ hs₀)
  exact hcon s (multipartitionQuartets_subset_edgeQuartets hT A hs)

theorem RunBy.isLimit (R : RunBy N g f T₀ o α β) :
    IsLimit α (edgeTestP o f T₀) (treeTestP o f) (afterStarBy o β g T₀) (limitTree N T₀) := by
  have hsub : afterStarBy o β g T₀ ⊆ T₀ := afterStarBy_subset
  refine ⟨R.limitTree_subset_afterStarBy, fun A hA => compl_mem_limitTree R.isTree hA, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro A hA h
    exact mem_limitTree.2 ⟨hsub hA, Or.inl h⟩
  · intro A hA
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hA
    exact isSplitFamily_contractSides (isSplitFamily_of_internal R.isTree h₂.1)
      (Finset.filter_subset _ _)
  · intro T hT A hAi hA
    refine (R.edge T (hT.trans hsub) A hAi).1 fun s hs => ?_
    obtain ⟨_, h₂⟩ := mem_internalSides.1 hAi
    rcases (mem_limitTree.1 hA).2 with h | ⟨_, h⟩
    · exact absurd h₂ h
    · exact h s (mem_filter.2 ⟨mem_univ _, mem_of_mem_edgeQuartets hs⟩)
  · intro T hT _ A hAi hA
    obtain ⟨hAT, h₂⟩ := mem_internalSides.1 hAi
    exact (R.edge T (hT.trans hsub) A hAi).2 (R.exists_not_null_edgeQuartets (hT.trans hsub)
      (hT hAT) h₂ hA)
  · intro T hT
    refine (R.tree T (hT.trans (limitTree_subset T₀))).1 fun s hs => ?_
    obtain ⟨A, hA, hAs⟩ := (mem_filter.1 hs).2
    rcases (mem_limitTree.1 (hT hA)).2 with h | ⟨_, h⟩
    · exact absurd (two_le_card_of_inter_taxa_mem hAs) h
    · exact h s (mem_filter.2 ⟨mem_univ _, hAs⟩)
  · intro T hT A hAi hA
    obtain ⟨hAT, h₂⟩ := mem_internalSides.1 hAi
    obtain ⟨s, hs, hn⟩ := R.exists_not_null_bipartition (hT hAT) h₂ hA
    exact (R.tree T (hT.trans hsub)).2 ⟨s, mem_filter.2 ⟨mem_univ _, A, hAT, (mem_filter.1 hs).2⟩, hn⟩

/-- On tables on which every test comes out right, the algorithm outputs the limit tree. -/
theorem RunBy.ectoblobBy_eq (R : RunBy N g f T₀ o α β) : ectoblobBy o α β g f T₀ = limitTree N T₀ :=
  R.isLimit.outputBy_eq o.rule

end Deterministic

/-! ### One combined test, at any level -/

section Probability

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}

omit [Fintype X] in
/-- One combined test comes out right with probability `> 1 - ε` for large `n`, as
`ECToBlob.eventually_testCorrect`, with the power of the test against the level itself in the place of the `o(n)` growth of
its statistic. -/
theorem eventually_testCorrect_of_level (hd : IsDist dist) (m : TestCorrection) {K : ℕ} {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop (𝓝[>] 0)) (Q : Finset (QuartetTree X)) (hK : Q.card ≤ K)
    (Null : QuartetTree X → Prop) (f : QuartetTree X → (n : ℕ) → (Fin n → Γ) → ℝ)
    (h01 : ∀ s n ω, 0 ≤ f s n ω ∧ f s n ω ≤ 1)
    (hnull : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n in atTop, 1 - ε <
      iidProb dist n fun ω => ∀ s ∈ Q, Null s →
        δ ≤ f s n ω ∧ ((m = .cauchy ∨ m = .cbc) → f s n ω ≤ 1 - δ))
    (halt : ∀ s ∈ Q, ¬ Null s → ∀ c : ℝ, 0 < c →
      Tendsto (fun n => iidProb dist n fun ω => f s n ω < c * τ n) atTop (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 - ε < iidProb dist n fun ω =>
      TestCorrect Null Q (τ n) (combineP m (Q.val.map fun s => f s n ω)) := by
  have hτ₀ : Tendsto τ atTop (𝓝 0) := hτ.mono_right nhdsWithin_le_nhds
  by_cases hall : ∀ s ∈ Q, Null s
  · -- the quartets are all under the null
    obtain ⟨δ, h0, h1, hev⟩ := hnull ε hε
    obtain ⟨c₀, -, hcomb⟩ := exists_combineBounds m 0 h0 (by linarith)
    filter_upwards [hev, hτ.eventually hcomb, hτ₀.eventually_lt_const h0] with n hn hc hlt
    refine hn.trans_le (iidProb_mono hd fun ω hω => ⟨fun _ => ?_, ?_⟩)
    · exact hc.gt_map Q (fun s => f s n ω) (fun s _ => h01 s n ω)
        (fun s hs => hlt.trans_le (hω s hs (hall s hs)).1) (fun hm s hs => (hω s hs (hall s hs)).2 hm)
    · rintro ⟨s, hs, hns⟩
      exact absurd (hall s hs) hns
  · -- a quartet is off the null
    push Not at hall
    obtain ⟨δ, h0, h1, hev⟩ := hnull (ε / 2) (half_pos hε)
    obtain ⟨c₀, hc₀, hcomb⟩ := exists_combineBounds m K h0 (by linarith)
    have hη : ∀ᶠ n in atTop, c₀ * τ n ≤ 1 - δ := by
      have h : Tendsto (fun n => c₀ * τ n) atTop (𝓝 (c₀ * 0)) := hτ₀.const_mul c₀
      rw [mul_zero] at h
      exact (h.eventually_lt_const (show (0 : ℝ) < 1 - δ by linarith)).mono fun _ h => h.le
    have halts : ∀ᶠ n in atTop, 1 - ε / 2 < iidProb dist n fun ω =>
        ∀ s ∈ Q.filter fun s => ¬ Null s, f s n ω < c₀ * τ n :=
      eventually_forall_mem hd _ (fun s n ω => f s n ω < c₀ * τ n) (half_pos hε) fun s hs ε' hε' =>
        (halt s (Finset.mem_filter.1 hs).1 (Finset.mem_filter.1 hs).2 c₀ hc₀).eventually_const_lt
          (by linarith)
    filter_upwards [hev, halts, hτ.eventually hcomb, hη] with n h₁ h₂ hc hηn
    refine (iidProb_and_gt hd n _ _ h₁ h₂).trans_le (iidProb_mono hd fun ω hω => ?_)
    obtain ⟨hω₁, hω₂⟩ := hω
    have hbelow : ∀ s ∈ Q, ¬ Null s → f s n ω < c₀ * τ n := fun s hs hn =>
      hω₂ s (Finset.mem_filter.2 ⟨hs, hn⟩)
    refine ⟨fun h => ?_, fun _ => ?_⟩
    · obtain ⟨s, hs, hns⟩ := hall
      exact absurd (h s hs) hns
    · obtain ⟨s₀, hs₀, hn₀⟩ := hall
      refine hc.lt_map Q hK (fun s => f s n ω) (fun s _ => h01 s n ω) ⟨s₀, hs₀, hbelow s₀ hs₀ hn₀⟩ ?_
      intro hm s hs
      by_cases hn : Null s
      · exact (hω₁ s hs hn).2 hm
      · exact (hbelow s hs hn).le.trans hηn

/-- From growth of the statistic to the power at a level: if the p-value is below `exp(-b_n/2)` for each `b_n = o(n)`, then
it is below any constant times a level whose logarithm is `o(n)`. -/
theorem tendsto_lt_level_of_growth {p : (n : ℕ) → (Fin n → Γ) → ℝ} {τ : ℕ → ℝ}
    (hτ : ∀ᶠ n in atTop, 0 < τ n) (hlog : Tendsto (fun n : ℕ => Real.log (τ n) / n) atTop (𝓝 0))
    (h : ∀ b : ℕ → ℝ, Tendsto (fun n : ℕ => b n / n) atTop (𝓝 0) →
      Tendsto (fun n => iidProb dist n fun ω => p n ω < Real.exp (-(b n) / 2)) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => iidProb dist n fun ω => p n ω < c * τ n) atTop (𝓝 1) := by
  have hb : Tendsto (fun n : ℕ => -2 * Real.log (c * τ n) / n) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n : ℕ => Real.log c / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h₂ := (h₁.add hlog).const_mul (-2 : ℝ)
    simp only [add_zero, mul_zero] at h₂
    refine h₂.congr' ?_
    filter_upwards [hτ] with n hn
    rw [Real.log_mul hc.ne' hn.ne']
    ring
  refine (h _ hb).congr' ?_
  filter_upwards [hτ] with n hn
  have hx : 0 < c * τ n := mul_pos hc hn
  have hexp : Real.exp (-(-2 * Real.log (c * τ n)) / 2) = c * τ n := by
    rw [show -(-2 * Real.log (c * τ n)) / 2 = Real.log (c * τ n) by ring, Real.exp_log hx]
  simp only [hexp]

end Probability

/-! ### What the proof of Theorem 8.2 needs of the tests -/

section Adequate

variable {V E X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ]

/-- **What the proof of Theorem 8.2 needs of the input p-values**, for the combination method `m`, at the levels `α_n`,
`β_n`. The null of the star test at a quartet is a trivial 4-blob, and the null of the T1 test is a cut split or a trivial
4-blob, of the network induced on its four taxa. -/
structure AdequateTests (N : RootedNetwork V E X) (dist : Γ → ℝ) (m : TestCorrection) (α β : ℕ → ℝ)
    (g f : QuartetTree X → (n : ℕ) → (Fin n → Γ) → ℝ) : Prop where
  star_mem : ∀ s n ω, 0 ≤ g s n ω ∧ g s n ω ≤ 1
  t1_mem : ∀ s n ω, 0 ≤ f s n ω ∧ f s n ω ≤ 1
  star_null : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n in atTop, 1 - ε <
    iidProb dist n fun ω => ∀ s, HasTrivialFourBlob N s.taxa →
      δ ≤ g s n ω ∧ ((m = .cauchy ∨ m = .cbc) → g s n ω ≤ 1 - δ)
  star_alt : ∀ s, ¬ HasTrivialFourBlob N s.taxa → ∀ c : ℝ, 0 < c →
    Tendsto (fun n => iidProb dist n fun ω => g s n ω < c * β n) atTop (𝓝 1)
  t1_null : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n in atTop, 1 - ε <
    iidProb dist n fun ω => ∀ s, IsNullQuartet N s →
      δ ≤ f s n ω ∧ ((m = .cauchy ∨ m = .cbc) → f s n ω ≤ 1 - δ)
  t1_alt : ∀ s, ¬ IsNullQuartet N s → ∀ c : ℝ, 0 < c →
    Tendsto (fun n => iidProb dist n fun ω => f s n ω < c * α n) atTop (𝓝 1)

variable {N : RootedNetwork V E X} {dist : Γ → ℝ} {m : TestCorrection} {α β : ℕ → ℝ}
  {g f : QuartetTree X → (n : ℕ) → (Fin n → Γ) → ℝ}

/-- **The conclusion of Theorem 8.2 for any adequate tests, on an arbitrary tree `T₀`.** With probability tending to one
the output is the limit tree. The proof is the paper's (lines 1047-1158): each test comes out right, by the union bound
they all do, and then the output is the limit tree. -/
theorem tendsto_ectoblobBy_limitTree (hN : N.IsPhylogenetic) (hd : IsDist dist)
    (hα : Tendsto α atTop (𝓝[>] 0)) (hβ : Tendsto β atTop (𝓝[>] 0))
    (h : AdequateTests N dist m α β g f) {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀)
    {o : ECToBlobOptions} (hm : o.testCo = m) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobBy o (α n) (β n) (fun s => g s n ω) (fun s => f s n ω) T₀ = limitTree N T₀)
      atTop (𝓝 1) := by
  subst hm
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  swap
  · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha
  have hε : 0 < 1 - a := by linarith
  -- the star tests
  have hS := eventually_forall_mem hd (internalSides T₀)
    (fun A n ω => TestCorrect (fun s => HasTrivialFourBlob N s.taxa) (multipartitionQuartets T₀ A)
      (β n) (edgeStarBy o (fun s => g s n ω) T₀ A))
    (half_pos hε) fun A hA ε' hε' => eventually_testCorrect_of_level hd o.testCo hβ _
      (card_multipartitionQuartets_le hT₀ (Finset.mem_filter.1 hA).1)
      (fun s => HasTrivialFourBlob N s.taxa) g h.star_mem
      (fun ε'' hε'' => by
        obtain ⟨δ, h0, h1, hev⟩ := h.star_null ε'' hε''
        exact ⟨δ, h0, h1, hev.mono fun n hn => hn.trans_le (iidProb_mono hd fun ω hω s _ hs => hω s hs)⟩)
      (fun s _ hs c hc => h.star_alt s hs c hc) hε'
  -- the T1 tests
  let tests := (T₀.powerset.sigma fun T => internalSides T).disjSum T₀.powerset
  let quartets : (Σ _ : Finset (Finset X), Finset X) ⊕ Finset (Finset X) →
      Finset (QuartetTree X) :=
    Sum.elim (fun i => edgeQuartets o T₀ i.1 i.2) fun T => Finset.univ.filter fun s => Displays T s
  have hK : ∀ i ∈ tests, (quartets i).card ≤ (Fintype.card X).choose 4 := by
    rintro (⟨T, A⟩ | T) hi
    · obtain ⟨hT, hA⟩ := Finset.mem_sigma.1 (Finset.inl_mem_disjSum.1 hi)
      exact card_edgeQuartets_le hT₀ (Finset.mem_powerset.1 hT) (Finset.mem_filter.1 hA).1
    · exact card_displays_le hT₀ (Finset.mem_powerset.1 (Finset.inr_mem_disjSum.1 hi))
  have hT := eventually_forall_mem hd tests (fun i n ω => TestCorrect
      (IsNullQuartet N) (quartets i) (α n)
      (combineP o.testCo ((quartets i).val.map fun s => f s n ω)))
    (half_pos hε) fun i hi ε' hε' => eventually_testCorrect_of_level hd o.testCo hα _ (hK i hi)
      (IsNullQuartet N) f h.t1_mem
      (fun ε'' hε'' => by
        obtain ⟨δ, h0, h1, hev⟩ := h.t1_null ε'' hε''
        exact ⟨δ, h0, h1, hev.mono fun n hn => hn.trans_le (iidProb_mono hd fun ω hω s _ hs => hω s hs)⟩)
      (fun s _ hs c hc => h.t1_alt s hs c hc) hε'
  filter_upwards [hS, hT] with n hnS hnT
  have hand := iidProb_and_gt hd n _ _ hnS hnT
  refine (by linarith : a ≤ 1 - (1 - a)).trans_lt (hand.trans_le (iidProb_mono hd fun ω hω => ?_))
  have R : RunBy N (fun s => g s n ω) (fun s => f s n ω) T₀ o (α n) (β n) := by
    refine ⟨hN, hT₀, hω.1, fun T hT A hA => ?_, fun T hT => ?_⟩
    · exact hω.2 (Sum.inl ⟨T, A⟩) (Finset.inl_mem_disjSum.2
        (Finset.mem_sigma.2 ⟨Finset.mem_powerset.2 hT, hA⟩))
    · exact hω.2 (Sum.inr T) (Finset.inr_mem_disjSum.2 (Finset.mem_powerset.2 hT))
  exact R.ectoblobBy_eq

/-- (`ecto:sec10_any_test`) **Lines 1419-1423: the conclusion of Theorem 8.2 for any adequate tests.** Given a resolution `T₀` of the tree of
blobs, the output is the tree of blobs with probability tending to one. -/
theorem consistency_ectoblobBy (hN : N.IsPhylogenetic) (hd : IsDist dist)
    (hα : Tendsto α atTop (𝓝[>] 0)) (hβ : Tendsto β atTop (𝓝[>] 0))
    (h : AdequateTests N dist m α β g f) {T₀ : Finset (Finset X)}
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) {o : ECToBlobOptions} (hm : o.testCo = m) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobBy o (α n) (β n) (fun s => g s n ω) (fun s => f s n ω) T₀ = treeOfBlobs N)
      atTop (𝓝 1) := by
  rw [← limitTree_eq_treeOfBlobs hN hT₀]
  exact tendsto_ectoblobBy_limitTree hN hd hα hβ h hT₀.1 hm

end Adequate

/-! ### Theorem 8.2 at other levels -/

section Levels

universe w

variable {V E X : Type w} [Fintype X] [DecidableEq X] {dist : BinaryGeneTree X → ℝ}

/-- The sequence `α_n` of the proof tends to zero from above. -/
theorem tendsto_alphaSeq_nhdsGT : Tendsto alphaSeq atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_alphaSeq, eventually_alphaSeq_pos⟩

/-- The sequence `β_n` of the proof tends to zero from above. -/
theorem tendsto_betaSeq_nhdsGT : Tendsto betaSeq atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_betaSeq, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  show 0 < betaSeq n
  rw [betaSeq_eq hn]
  positivity

/-- The star test under the null, on all the quartets at once: Lemma 8.1 (lines 1064-1077). -/
theorem exists_delta_star_univ (hd : IsDist dist) (k : StarTest) (m : TestCorrection) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, 1 - ε < iidProb dist n fun ω =>
      ∀ s : QuartetTree X, IsUniformOn (displayCF dist Subtype.val) s.taxa →
        δ ≤ starPValue k (quartetCount Subtype.val ω) s.taxa ∧
          ((m = .cauchy ∨ m = .cbc) →
            starPValue k (quartetCount Subtype.val ω) s.taxa ≤ 1 - δ) := by
  let ι₀ := {s : QuartetTree X // IsUniformOn (displayCF dist Subtype.val) s.taxa}
  let fam : ι₀ → (n : ℕ) → (Fin n → BinaryGeneTree X) → ℝ :=
    fun s _ ω => starPValue k (quartetCount Subtype.val ω) s.1.taxa
  have hone := displaysOne_binaryGeneTree dist
  obtain ⟨δ, h0, h1, h⟩ := lemma8_1.{w, w} (Fintype.card ι₀ + 1) (by omega) hε
  have hmem : ∀ (s : ι₀) (n : ℕ) (ω : Fin n → BinaryGeneTree X), 0 ≤ fam s n ω ∧ fam s n ω ≤ 1 := by
    intro s n ω
    have hc : ∀ r, 0 ≤ quartetCount Subtype.val ω r := fun r => quartetCount_nonneg ω r
    show 0 ≤ starPValue k _ _ ∧ starPValue k _ _ ≤ 1
    cases k with
    | lrt => exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
        have := starStat_nonneg _ hc s.1.card_taxa
        linarith)⟩
    | pearson => exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
        have : 0 ≤ pearsonStat (quartetCount Subtype.val ω) s.1.taxa :=
          Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _)
            (div_nonneg (Finset.sum_nonneg fun t _ => hc t) (by norm_num))
        linarith)⟩
  obtain ⟨M, hM⟩ := h dist fam hd (by omega) hmem
    (fun s => starPValue_asymptoticallyUniform k hd hone s.1.card_taxa s.2)
  refine ⟨δ, h0, h1, ?_⟩
  filter_upwards [eventually_gt_atTop M] with n hn
  refine (hM n hn).trans_le (iidProb_mono hd fun ω hω s hu => ?_)
  exact ⟨(hω ⟨s, hu⟩).1, fun _ => (hω ⟨s, hu⟩).2⟩

/-- The tests of the paper are adequate at any levels with `o(n)` cutoffs. -/
theorem adequateTests_levels {N : RootedNetwork V E X} (hd : IsDist dist)
    (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {α β : ℕ → ℝ} (hαpos : ∀ᶠ n in atTop, 0 < α n) (hβpos : ∀ᶠ n in atTop, 0 < β n)
    (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    AdequateTests N dist o.testCo α β
      (fun s _ ω => starPValue o.starTest (quartetCount Subtype.val ω) s.taxa)
      (fun s _ ω => t1PValue (quartetCount Subtype.val ω) s) := by
  have hone := displaysOne_binaryGeneTree dist
  have hsum : ∀ s : QuartetTree X, ∑ r ∈ treesOn s.taxa, displayCF dist Subtype.val r = 1 :=
    fun s => sum_displayCF_binaryGeneTree hd s.card_taxa
  refine ⟨fun s n ω => ?_, fun s n ω => t1PValue_mem _ s, fun ε hε => ?_, fun s hs c hc => ?_,
    fun ε hε => ?_, fun s hs c hc => ?_⟩
  · have hc : ∀ r, 0 ≤ quartetCount Subtype.val ω r := fun r => quartetCount_nonneg ω r
    cases o.starTest with
    | lrt => exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
        have := starStat_nonneg _ hc s.card_taxa
        linarith)⟩
    | pearson => exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
        have : 0 ≤ pearsonStat (quartetCount Subtype.val ω) s.taxa :=
          Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _)
            (div_nonneg (Finset.sum_nonneg fun t _ => hc t) (by norm_num))
        linarith)⟩
  · -- the star test under the null, on all the quartets at once
    obtain ⟨δ, h0, h1, hev⟩ := exists_delta_star_univ hd o.starTest o.testCo hε
    refine ⟨δ, h0, h1, ?_⟩
    filter_upwards [hev] with n hn
    exact hn.trans_le (iidProb_mono hd fun ω hω s hs => hω s (h₁.star _ s.card_taxa hs))
  · refine tendsto_lt_level_of_growth hβpos hβ (fun b hb => ?_) hc
    refine starStat_growth o.starTest hd hone s.card_taxa (fun hu => hs ?_) hb
    exact (uniform_iff h₁ h₂ s).1 hu
  · obtain ⟨δ, h0, h1, hev⟩ := exists_delta_t1 hd o.testCo hpos (Finset.univ) hε
    refine ⟨δ, h0, h1, ?_⟩
    filter_upwards [hev] with n hn
    refine hn.trans_le (iidProb_mono hd fun ω hω s hs => ?_)
    exact hω s (Finset.mem_univ s) ((t1Null_iff h₁ h₂ hsum s).2 hs)
  · refine tendsto_lt_level_of_growth hαpos hα (fun b hb => ?_) hc
    exact t1PValue_growth hd hone (fun hn => hs ((t1Null_iff h₁ h₂ hsum s).1 hn)) hb

/-- (`ecto:thm8_2_levels`) **Theorem 8.2 at other levels (lines 1159-1167).** "While specific choices for `α_n` and `β_n` were made in our proof,
others could be used instead": any `α_n, β_n → 0` from above whose cutoffs are `o(n)`, in the sense that `log α_n / n → 0`
and `log β_n / n → 0`. The hypotheses on the law are those of `ECToBlob.theorem8_2`. -/
theorem theorem8_2_levels (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ)
    (hd : IsDist dist) (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r)
    {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝[>] 0)) (hβ₀ : Tendsto β atTop (𝓝[>] 0))
    (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblob o (α n) (β n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) :=
  consistency_ectoblobBy hN hd hα₀ hβ₀
    (adequateTests_levels hd h₁ h₂ o hpos (hα₀.eventually self_mem_nhdsWithin)
      (hβ₀.eventually self_mem_nhdsWithin) hα hβ) hT₀ rfl

/-- The level of the BIC for the star test, at line 1162: `β_n = 1/n`, the upper tail of `χ²₂` at `2 log n`. -/
theorem chiSqTwoTail_two_mul_log {n : ℕ} (hn : 0 < n) : chiSqTwoTail (2 * Real.log n) = 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold chiSqTwoTail
  rw [show -(2 * Real.log (n : ℝ)) / 2 = -Real.log n by ring, Real.exp_neg, Real.exp_log hn', one_div]

/-- (`ecto:thm8_2_bic`) **The choice of the BIC (lines 1160-1163).** Theorem 8.2 holds with `β_n = 1/n`, "instead of `β_n = 1/√n` used in the
proof". -/
theorem theorem8_2_bic (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) (dist : BinaryGeneTree X → ℝ)
    (hd : IsDist dist) (h₁ : Assumption1Forward N (displayCF dist Subtype.val))
    (h₂ : Assumption1Converse N (displayCF dist Subtype.val)) (T₀ : Finset (Finset X))
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) (o : ECToBlobOptions)
    (hpos : (o.testCo = .cauchy ∨ o.testCo = .cbc) →
      ∀ s, IsT1Strict (displayCF dist Subtype.val) s →
        ∀ r ∈ s.alternatives, 0 < displayCF dist Subtype.val r) :
    Tendsto (fun n : ℕ => iidProb dist n fun ω =>
      ectoblob o (alphaSeq n) (1 / n) (quartetCount Subtype.val ω) T₀ = treeOfBlobs N) atTop (𝓝 1) := by
  have hpos' : ∀ᶠ n : ℕ in atTop, 0 < (1 : ℝ) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h₀ : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop, hpos'⟩
  have hlog : Tendsto (fun n : ℕ => Real.log ((1 : ℝ) / n) / n) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h' := (h.comp tendsto_natCast_atTop_atTop).const_mul (-1 : ℝ)
    rw [mul_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp, pow_one, one_mul, add_zero, one_div, Real.log_inv]
    ring
  exact theorem8_2_levels N hN dist hd h₁ h₂ T₀ hT₀ o hpos
    (tendsto_nhdsWithin_iff.2 ⟨tendsto_alphaSeq, eventually_alphaSeq_pos⟩) h₀
    tendsto_log_chiSqOneTail_log hlog

end Levels

end ECToBlob.Framework
