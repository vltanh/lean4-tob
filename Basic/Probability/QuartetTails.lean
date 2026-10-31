module

public import Basic.Probability.IID
public import Basic.Probability.GaussianTail
public import Basic.Phylogenetics.TreeSplits
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The quartet hypothesis tests: tail bounds and growth under the alternative

For a sample of `n` gene trees, whose displayed quartet trees on a set of four taxa have probabilities
`p`, this file gives the elementary bounds on the test distributions and, from the law of large numbers,
the growth of the statistics under the alternative (Shao 2003, §6.4.2, for the likelihood ratio; §6.5.4,
for Pearson's statistic), as ECToBlob §8 and TINNiK's proof of Theorem 4 use.
-/

@[expose] public noncomputable section

open Phylogenetics Finset Filter Topology
open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Phylogenetics.QuartetTests

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ]

/-- `f (ω)` of the sample `ω`, a real function of the sample, is asymptotically uniformly distributed
on `[0,1]` for samples from `dist`: its distribution function converges to that of the uniform law. -/
def AsymptoticallyUniform (dist : Γ → ℝ) (f : (n : ℕ) → (Fin n → Γ) → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Tendsto (fun n => iidProb dist n fun ω => f n ω ≤ x) atTop (𝓝 x)

variable {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-- The gene trees of positive probability are binary, so each displays exactly one quartet tree on
each set of four taxa. -/
def DisplaysOne (dist : Γ → ℝ) (sides : Γ → Finset (Finset X)) : Prop :=
  ∀ (g : Γ), dist g ≠ 0 → ∀ q : Finset X, q.card = 4 → ∃! s, s ∈ treesOn q ∧ Displays (sides g) s

/-! ### The test distributions -/

/-- `χ²₂` is the law of `Z₁² + Z₂²`. -/
theorem chiSqTwoTail_eq {t : ℝ} (ht : 0 ≤ t) :
    chiSqTwoTail t =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).real {z : ℝ × ℝ | t < z.1 ^ 2 + z.2 ^ 2} :=
  (gaussianReal_prod_real_lt_sq_add_sq ht).symm

/-- The tail of `χ²₁` through a product with any probability measure. -/
private lemma chiSqOneTail_eq_prod (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    chiSqOneTail t = ((gaussianReal 0 1).prod ν).real ({z : ℝ | t < z ^ 2} ×ˢ Set.univ) := by
  rw [measureReal_prod_prod]
  simp [chiSqOneTail]

/-- The lower bound of the T1 test distribution: `Z²` is at most its variable. -/
theorem chiSqOneTail_le_t1Tail (μ t : ℝ) : chiSqOneTail t ≤ t1Tail μ t := by
  rw [chiSqOneTail_eq_prod (gaussianReal μ 1)]
  refine measureReal_mono ?_
  rintro ⟨x, y⟩ ⟨hx, -⟩
  have hx' : t < x ^ 2 := hx
  show t < x ^ 2 + if y < 0 then y ^ 2 else 0
  split_ifs <;> nlinarith [sq_nonneg y]

/-- The upper bound: writing `Z̄ = Z̄₀ + μ` for a standard Gaussian `Z̄₀`, the extra term
`½ (1 - sgn Z̄) Z̄²` is at most `Z̄₀²` for `μ ≥ 0`, so the variable is at most `Z² + Z̄₀²`. -/
theorem t1Tail_le_chiSqTwoTail {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) : t1Tail μ t ≤ chiSqTwoTail t := by
  rw [chiSqTwoTail_eq ht]
  unfold t1Tail
  set T := {z : ℝ × ℝ | t < z.1 ^ 2 + if z.2 < 0 then z.2 ^ 2 else 0} with hTdef
  have hT : MeasurableSet T := by
    refine measurableSet_lt measurable_const ((measurable_fst.pow_const 2).add
      (Measurable.ite ?_ (measurable_snd.pow_const 2) measurable_const))
    exact measurableSet_lt measurable_snd measurable_const
  have hmap : gaussianReal μ 1 = (gaussianReal 0 1).map (· + μ) := by
    rw [gaussianReal_map_add_const]; simp
  have hprod : (gaussianReal 0 1).prod (gaussianReal μ 1) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (Prod.map id (· + μ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, ← hmap]
  rw [hprod, map_measureReal_apply (by fun_prop) hT]
  refine measureReal_mono ?_
  rintro ⟨x, y⟩ h
  have h' : t < x ^ 2 + if y + μ < 0 then (y + μ) ^ 2 else 0 := h
  show t < x ^ 2 + y ^ 2
  split_ifs at h' with hy
  · nlinarith
  · nlinarith [sq_nonneg y]

theorem chiSqOneTail_nonneg (t : ℝ) : 0 ≤ chiSqOneTail t := measureReal_nonneg

theorem chiSqOneTail_le_one (t : ℝ) : chiSqOneTail t ≤ 1 := by
  unfold chiSqOneTail
  calc _ ≤ (gaussianReal 0 1).real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = 1 := probReal_univ

theorem chiSqOneTail_le_chiSqTwoTail {t : ℝ} (ht : 0 ≤ t) : chiSqOneTail t ≤ chiSqTwoTail t :=
  (chiSqOneTail_le_t1Tail 0 t).trans (t1Tail_le_chiSqTwoTail le_rfl ht)

/-- The tail of `χ²₁` is strictly decreasing on `[0, ∞)`. -/
theorem chiSqOneTail_lt_of_lt {t t' : ℝ} (ht : 0 ≤ t) (htt : t < t') :
    chiSqOneTail t' < chiSqOneTail t := by
  have hsq : ∀ z : ℝ, √t < z → t < z ^ 2 := fun z hz => Real.lt_sq_of_sqrt_lt hz
  have hlt : √t < √t' := Real.sqrt_lt_sqrt ht htt
  have hpos := gaussianReal_real_Ioo_pos hlt
  have hdisj : Disjoint {z : ℝ | t' < z ^ 2} (Set.Ioo (√t) (√t')) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨h1, h2⟩
    have hz0 : 0 ≤ z := (Real.sqrt_nonneg t).trans h1.le
    have : z ^ 2 < t' := by
      have := (Real.lt_sqrt hz0).1 h2
      exact this
    exact absurd (show t' < z ^ 2 from hz) (not_lt.2 this.le)
  have hunion := measureReal_union (μ := gaussianReal 0 1) hdisj measurableSet_Ioo
  have hsub : {z : ℝ | t' < z ^ 2} ∪ Set.Ioo (√t) (√t') ⊆ {z : ℝ | t < z ^ 2} := by
    rintro z (hz | hz)
    · exact htt.trans hz
    · exact hsq z hz.1
  have hle := measureReal_mono (μ := gaussianReal 0 1) hsub
  unfold chiSqOneTail
  linarith

/-- The Gaussian lower bound for the tail of `χ²₁`. -/
theorem gaussianPDFReal_le_chiSqOneTail (t : ℝ) :
    gaussianPDFReal 0 1 (√t + 1) ≤ chiSqOneTail t := by
  refine (gaussianPDFReal_le_gaussianReal_real_Ioo (Real.sqrt_nonneg t)).trans
    (measureReal_mono fun z hz => ?_)
  exact Real.lt_sq_of_sqrt_lt hz.1

theorem chiSqOneTail_pos (t : ℝ) : 0 < chiSqOneTail t :=
  (gaussianPDFReal_pos _ _ _ one_ne_zero).trans_le (gaussianPDFReal_le_chiSqOneTail t)

/-- The cut test distribution has tail at most that of `χ²₁`: its variable is at most `Z²`. -/
theorem cutTail_le_chiSqOneTail (φ n t : ℝ) : cutTail φ n t ≤ chiSqOneTail t := by
  rw [chiSqOneTail_eq_prod (gaussianReal (muZero φ n) 1)]
  unfold cutTail
  refine measureReal_mono ?_
  rintro ⟨x, y⟩ h
  have h0 : t < min (x ^ 2) (min ((Real.sin (alphaZero φ) * x + Real.cos (alphaZero φ) * y) ^ 2)
      ((Real.sin (alphaZero φ) * x - Real.cos (alphaZero φ) * y) ^ 2)) := h
  exact ⟨lt_of_lt_of_le h0 (min_le_left _ _), Set.mem_univ _⟩

/-! ### The statistics: nonnegativity -/

private lemma sub_le_mul_log_sub {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) :
    c - m ≤ c * Real.log c - c * Real.log m := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using hm.le
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hm hc)
    rw [Real.log_div hm.ne' hc.ne'] at h1
    have h2 : c * (Real.log m - Real.log c) ≤ c * (m / c - 1) := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * (m / c - 1) = m - c := by field_simp
    linarith

private lemma sub_lt_mul_log_sub {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hne : c ≠ m) :
    c - m < c * Real.log c - c * Real.log m := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using hm
  · have h0 : m / c ≠ 1 := fun h => hne ((div_eq_one_iff_eq hc.ne').1 h).symm
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hm hc) h0
    rw [Real.log_div hm.ne' hc.ne'] at h1
    have h2 : c * (Real.log m - Real.log c) < c * (m / c - 1) := mul_lt_mul_of_pos_left h1 hc
    have h3 : c * (m / c - 1) = m - c := by field_simp
    linarith

private lemma log_add_eq {a b : ℝ} (h : 0 < a + b) :
    Real.log (a + b) = Real.log ((a + b) / 2) + Real.log 2 := by
  rw [← Real.log_mul (by positivity) (by norm_num)]
  congr 1
  ring

private lemma pair_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a * Real.log a + b * Real.log b - (a + b) * Real.log (a + b) + (a + b) * Real.log 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · have hm : 0 < (a + b) / 2 := by positivity
    have h1 := sub_le_mul_log_sub ha hm
    have h2 := sub_le_mul_log_sub hb hm
    rw [log_add_eq h]
    nlinarith

private lemma pair_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b) :
    0 < a * Real.log a + b * Real.log b - (a + b) * Real.log (a + b) + (a + b) * Real.log 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    exact absurd (ha0.trans hb0.symm) hne
  · have hm : 0 < (a + b) / 2 := by positivity
    have h1 := sub_lt_mul_log_sub ha hm (fun h' => hne (by linarith))
    have h2 := sub_le_mul_log_sub hb hm
    rw [log_add_eq h]
    nlinarith

/-- The two alternatives of a quartet tree. -/
theorem QuartetTree.exists_alternatives (s : QuartetTree X) :
    ∃ r r', r ≠ r' ∧ s.alternatives = {r, r'} :=
  Finset.card_eq_two.1 s.card_alternatives

theorem mem_treesOn_taxa_of_mem_alternatives {s r : QuartetTree X} (h : r ∈ s.alternatives) :
    r ∈ treesOn s.taxa := by
  simp only [QuartetTree.alternatives, Finset.mem_filter, Finset.mem_univ, true_and] at h
  simp [treesOn, h.1]

theorem mem_treesOn_taxa (s : QuartetTree X) : s ∈ treesOn s.taxa := by
  simp [treesOn]

theorem lineStat_nonneg (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    0 ≤ lineStat c s := by
  obtain ⟨r, r', hne, h⟩ := QuartetTree.exists_alternatives s
  unfold lineStat
  rw [h, Finset.sum_pair hne, Finset.sum_pair hne]
  have := pair_nonneg (hc r) (hc r')
  linarith

theorem lineStat_pos (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X)
    (hne : ∃ r ∈ s.alternatives, ∃ r' ∈ s.alternatives, c r ≠ c r') : 0 < lineStat c s := by
  obtain ⟨r, r', hrr, h⟩ := QuartetTree.exists_alternatives s
  obtain ⟨u, hu, u', hu', huu⟩ := hne
  have hcne : c r ≠ c r' := by
    rw [h] at hu hu'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
    · exact absurd rfl huu
    · exact huu
    · exact huu.symm
    · exact absurd rfl huu
  unfold lineStat
  rw [h, Finset.sum_pair hrr, Finset.sum_pair hrr]
  have := pair_pos (hc r) (hc r') hcne
  linarith

/-- The likelihood ratio statistic of the star test, written against the mean count. -/
private lemma starStat_sum {q : Finset X} (hq : q.card = 4) (c : QuartetTree X → ℝ) {m : ℝ}
    (hm : m = (∑ r ∈ treesOn q, c r) / 3) :
    (∑ r ∈ treesOn q, (c r - m)) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, card_treesOn hq, hm]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

private lemma starStat_eq_sum (c : QuartetTree X → ℝ) (q : Finset X) :
    starStat c q = 2 * ∑ r ∈ treesOn q,
      (c r * Real.log (c r) - c r * Real.log ((∑ t ∈ treesOn q, c t) / 3)) := by
  unfold starStat
  rw [Finset.sum_sub_distrib, Finset.sum_mul]

theorem starStat_nonneg (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) {q : Finset X} (hq : q.card = 4) :
    0 ≤ starStat c q := by
  have hS : 0 ≤ ∑ r ∈ treesOn q, c r := Finset.sum_nonneg fun r _ => hc r
  rcases hS.eq_or_lt with h | h
  · have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hc r).1 h.symm
    rw [starStat_eq_sum]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun r hr => ?_)
    simp [h0 r hr]
  · have hm : 0 < (∑ r ∈ treesOn q, c r) / 3 := by positivity
    rw [starStat_eq_sum]
    have h1 : (∑ r ∈ treesOn q, (c r - (∑ t ∈ treesOn q, c t) / 3)) ≤ ∑ r ∈ treesOn q,
        (c r * Real.log (c r) - c r * Real.log ((∑ t ∈ treesOn q, c t) / 3)) :=
      Finset.sum_le_sum fun r _ => sub_le_mul_log_sub (hc r) hm
    rw [starStat_sum hq c rfl] at h1
    linarith

theorem starStat_pos (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) {q : Finset X} (hq : q.card = 4)
    (hS : ∑ r ∈ treesOn q, c r = 1) (hne : ∃ r ∈ treesOn q, c r ≠ 1 / 3) : 0 < starStat c q := by
  have hm : 0 < (∑ r ∈ treesOn q, c r) / 3 := by rw [hS]; norm_num
  rw [starStat_eq_sum]
  obtain ⟨r₀, hr₀, hr₀'⟩ := hne
  have h1 : (∑ r ∈ treesOn q, (c r - (∑ t ∈ treesOn q, c t) / 3)) < ∑ r ∈ treesOn q,
      (c r * Real.log (c r) - c r * Real.log ((∑ t ∈ treesOn q, c t) / 3)) := by
    refine Finset.sum_lt_sum (fun r _ => sub_le_mul_log_sub (hc r) hm) ⟨r₀, hr₀, ?_⟩
    exact sub_lt_mul_log_sub (hc r₀) hm (by rw [hS]; simpa using hr₀')
  rw [starStat_sum hq c rfl] at h1
  linarith

/-- The T1 statistic and its estimated parameter are in range, so the tail bounds apply. -/
theorem t1Stat_nonneg (c : QuartetTree X → ℝ) (hc : ∀ r, 0 ≤ c r) (s : QuartetTree X) :
    0 ≤ t1Stat c s := by
  unfold t1Stat
  split_ifs
  · exact lineStat_nonneg c hc s
  · exact starStat_nonneg c hc s.card_taxa

theorem muZero_t1Phi_nonneg (c : QuartetTree X → ℝ) (s : QuartetTree X) :
    0 ≤ muZero (t1Phi c s) (c s + ∑ r ∈ s.alternatives, c r) := by
  unfold muZero
  refine div_nonneg (mul_nonneg (Real.sqrt_nonneg _) ?_) (Real.sqrt_nonneg _)
  have : t1Phi c s ≤ 1 := min_le_left _ _
  linarith

/-! ### Homogeneity and continuity of the statistics -/

private lemma mul_mul_log_mul (x : ℝ) {a : ℝ} (ha : a ≠ 0) :
    (a * x) * Real.log (a * x) = a * (x * Real.log x) + a * x * Real.log a := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_mul ha hx]; ring

omit [Fintype X] in
private lemma sum_mul_mul_log_mul (I : Finset (QuartetTree X)) (c : QuartetTree X → ℝ) {a : ℝ}
    (ha : a ≠ 0) :
    ∑ r ∈ I, (a * c r) * Real.log (a * c r) =
      a * ∑ r ∈ I, c r * Real.log (c r) + a * (∑ r ∈ I, c r) * Real.log a := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => mul_mul_log_mul _ ha

theorem lineStat_const_mul {a : ℝ} (ha : a ≠ 0) (c : QuartetTree X → ℝ) (s : QuartetTree X) :
    lineStat (fun r => a * c r) s = a * lineStat c s := by
  unfold lineStat
  rw [sum_mul_mul_log_mul _ c ha, ← Finset.mul_sum, mul_mul_log_mul _ ha]
  ring

theorem starStat_const_mul {a : ℝ} (ha : a ≠ 0) (c : QuartetTree X → ℝ) (q : Finset X) :
    starStat (fun r => a * c r) q = a * starStat c q := by
  unfold starStat
  rw [sum_mul_mul_log_mul _ c ha, ← Finset.mul_sum]
  set A := ∑ r ∈ treesOn q, c r
  have h := mul_mul_log_mul (A / 3) ha
  have h' : a * A / 3 = a * (A / 3) := by ring
  rw [h']
  linear_combination -6 * h

theorem pearsonStat_const_mul {a : ℝ} (ha : a ≠ 0) (c : QuartetTree X → ℝ) (q : Finset X) :
    pearsonStat (fun r => a * c r) q = a * pearsonStat c q := by
  unfold pearsonStat
  rw [Finset.mul_sum, ← Finset.mul_sum (treesOn q) c a]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hA : ∑ t ∈ treesOn q, c t = 0
  · simp [hA]
  · field_simp

theorem t1Stat_const_mul {a : ℝ} (ha : 0 < a) (c : QuartetTree X → ℝ) (s : QuartetTree X) :
    t1Stat (fun r => a * c r) s = a * t1Stat c s := by
  unfold t1Stat
  have h : (∑ r ∈ s.alternatives, a * c r) / 2 ≤ a * c s ↔ (∑ r ∈ s.alternatives, c r) / 2 ≤ c s := by
    rw [← Finset.mul_sum, mul_div_assoc]
    exact mul_le_mul_iff_right₀ ha
  by_cases h' : (∑ r ∈ s.alternatives, c r) / 2 ≤ c s
  · rw [ite_eq_left (h.2 h'), ite_eq_left h', lineStat_const_mul ha.ne']
  · rw [ite_eq_right (fun h'' => h' (h.1 h'')), ite_eq_right h', starStat_const_mul ha.ne']

omit [Fintype X] in
private lemma continuous_sum_apply (I : Finset (QuartetTree X)) :
    Continuous fun x : QuartetTree X → ℝ => ∑ r ∈ I, x r :=
  continuous_finsetSum _ fun r _ => continuous_apply r

omit [Fintype X] in
private lemma continuous_sum_mul_log (I : Finset (QuartetTree X)) :
    Continuous fun x : QuartetTree X → ℝ => ∑ r ∈ I, x r * Real.log (x r) :=
  continuous_finsetSum _ fun r _ => Real.continuous_mul_log.comp (continuous_apply r)

theorem continuous_lineStat (s : QuartetTree X) :
    Continuous fun x : QuartetTree X → ℝ => lineStat x s := by
  unfold lineStat
  exact continuous_const.mul (((continuous_sum_mul_log _).sub
    (Real.continuous_mul_log.comp (continuous_sum_apply _))).add
    ((continuous_sum_apply _).mul continuous_const))

theorem continuous_starStat (q : Finset X) :
    Continuous fun x : QuartetTree X → ℝ => starStat x q := by
  have h : (fun x : QuartetTree X → ℝ => starStat x q) = fun x =>
      2 * (∑ r ∈ treesOn q, x r * Real.log (x r) -
        3 * (((∑ r ∈ treesOn q, x r) / 3) * Real.log ((∑ r ∈ treesOn q, x r) / 3))) := by
    funext x
    unfold starStat
    ring
  rw [h]
  exact continuous_const.mul ((continuous_sum_mul_log _).sub (continuous_const.mul
    (Real.continuous_mul_log.comp ((continuous_sum_apply _).div_const 3))))

theorem continuousAt_pearsonStat (q : Finset X) {p : QuartetTree X → ℝ}
    (hp : ∑ r ∈ treesOn q, p r ≠ 0) :
    ContinuousAt (fun x : QuartetTree X → ℝ => pearsonStat x q) p := by
  unfold pearsonStat
  refine tendsto_finsetSum _ fun r _ => ?_
  have h1 : Continuous fun x : QuartetTree X → ℝ => (∑ t ∈ treesOn q, x t) / 3 :=
    (continuous_sum_apply _).div_const 3
  refine ContinuousAt.div ((((continuous_apply r).sub h1).pow 2).continuousAt) h1.continuousAt ?_
  exact div_ne_zero hp (by norm_num)

/-! ### Frequencies under the weak law -/

omit [Fintype X] in
theorem displayCF_nonneg (hd : IsDist dist) (r : QuartetTree X) : 0 ≤ displayCF dist sides r :=
  Finset.sum_nonneg fun g _ => by split_ifs <;> simp [hd.1 g]

/-- Under `DisplaysOne`, the concordance factors on four taxa sum to one. -/
theorem sum_displayCF_treesOn (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) : ∑ r ∈ treesOn q, displayCF dist sides r = 1 := by
  unfold displayCF
  rw [Finset.sum_comm, ← hd.2]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : dist g = 0
  · simp [hg]
  · obtain ⟨s, ⟨hs1, hs2⟩, huniq⟩ := hs g hg q hq
    rw [Finset.sum_eq_single s]
    · simp [hs2]
    · intro r hr hne
      rw [ite_eq_right]
      intro h
      exact hne (huniq r ⟨hr, h⟩)
    · intro h
      exact absurd hs1 h

omit [Fintype X] [Fintype Γ] in
theorem quartetCount_nonneg {n : ℕ} (ω : Fin n → Γ) (r : QuartetTree X) :
    0 ≤ quartetCount sides ω r := Nat.cast_nonneg _

omit [Fintype X] [Fintype Γ] in
private lemma quartetCount_eq_sum {n : ℕ} (ω : Fin n → Γ) (r : QuartetTree X) :
    quartetCount sides ω r = ∑ i, (if Displays (sides (ω i)) r then 1 else 0 : ℝ) := by
  simp only [quartetCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

omit [Fintype X] in
private lemma displayCF_eq_sum (r : QuartetTree X) :
    displayCF dist sides r = ∑ g, dist g * (if Displays (sides g) r then 1 else 0 : ℝ) := by
  simp [displayCF, mul_ite]

/-- **The weak law of large numbers** for the empirical frequencies of the displayed quartet trees: they
are in any neighbourhood of the concordance factors with probability tending to one. -/
theorem tendsto_iidProb_freq (hd : IsDist dist) {P : (QuartetTree X → ℝ) → Prop}
    (hP : ∀ᶠ x in 𝓝 (displayCF dist sides), P x) :
    Tendsto (fun n : ℕ => iidProb dist n fun ω => P fun r => quartetCount sides ω r / n)
      atTop (𝓝 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hP
  have h : Tendsto (fun n : ℕ => iidProb dist n fun ω : Fin n → Γ => ∀ r : QuartetTree X,
      |(∑ i, (if Displays (sides (ω i)) r then 1 else 0 : ℝ)) / n -
        ∑ g, dist g * (if Displays (sides g) r then 1 else 0 : ℝ)| < ε) atTop (𝓝 1) :=
    tendsto_iidProb_forall hd _ fun r =>
      iidProb_weak_law hd (fun g => if Displays (sides g) r then 1 else 0) hε
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => hball ?_) h
  rw [dist_pi_lt_iff hε]
  intro r
  rw [Real.dist_eq, quartetCount_eq_sum, displayCF_eq_sum]
  exact hω r

/-- A statistic of degree one which at the true frequencies exceeds `d` exceeds `n d` on the counts,
with probability tending to one. -/
private lemma tendsto_iidProb_stat_gt (hd : IsDist dist) (F : (QuartetTree X → ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ c, F (fun r => a * c r) = a * F c) {d : ℝ}
    (hF : ∀ᶠ x in 𝓝 (displayCF dist sides), d < F x) {b : ℕ → ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ n * d) :
    Tendsto (fun n => iidProb dist n fun ω => b n < F (quartetCount sides ω)) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_freq hd hF)
  filter_upwards [hb, eventually_gt_atTop 0] with n hn hn0 ω hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc : quartetCount sides ω = fun r => (n : ℝ) * (quartetCount sides ω r / n) := by
    funext r
    field_simp
  rw [hc, hhom _ hn']
  exact hn.trans_lt (mul_lt_mul_of_pos_left hω hn')

private lemma eventually_le_mul {b : ℕ → ℝ} (hb : Tendsto (fun n => b n / n) atTop (𝓝 0)) {d : ℝ}
    (hd : 0 < d) : ∀ᶠ n : ℕ in atTop, b n ≤ n * d := by
  filter_upwards [hb.eventually (gt_mem_nhds hd), eventually_gt_atTop 0] with n h1 h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast h2
  rw [div_lt_iff₀ hn'] at h1
  linarith

/-! ### Growth under the alternative -/

/-- Under the alternative of the star test, its statistic grows faster than any `b_n = o(n)`. -/
theorem starStat_growth (k : StarTest) (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ¬ ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) {b : ℕ → ℝ}
    (hb : Tendsto (fun n => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      Real.exp (-(b n) / 2) > starPValue k (quartetCount sides ω) q) atTop (𝓝 1) := by
  have hp0 : ∀ r, 0 ≤ displayCF dist sides r := displayCF_nonneg hd
  have hp1 := sum_displayCF_treesOn hd hs hq
  obtain ⟨r₀, hr₀, hne⟩ : ∃ r ∈ treesOn q, displayCF dist sides r ≠ 1 / 3 := by
    push Not at h
    exact h
  obtain ⟨F, hhom, hcont, hpos, hval⟩ : ∃ F : (QuartetTree X → ℝ) → ℝ,
      (∀ a : ℝ, 0 < a → ∀ c, F (fun r => a * c r) = a * F c) ∧
      ContinuousAt F (displayCF dist sides) ∧ 0 < F (displayCF dist sides) ∧
      ∀ c, starPValue k c q = chiSqTwoTail (F c) := by
    cases k with
    | lrt =>
      exact ⟨fun c => starStat c q, fun a ha c => starStat_const_mul ha.ne' c q,
        (continuous_starStat q).continuousAt, starStat_pos _ hp0 hq hp1 ⟨r₀, hr₀, hne⟩,
        fun c => rfl⟩
    | pearson =>
      refine ⟨fun c => pearsonStat c q, fun a ha c => pearsonStat_const_mul ha.ne' c q,
        continuousAt_pearsonStat q (by rw [hp1]; norm_num), ?_, fun c => rfl⟩
      show 0 < pearsonStat _ q
      unfold pearsonStat
      rw [hp1]
      refine Finset.sum_pos' (fun r _ => by positivity) ⟨r₀, hr₀, ?_⟩
      have : displayCF dist sides r₀ - 1 / 3 ≠ 0 := sub_ne_zero.2 hne
      positivity
  have hd2 : 0 < F (displayCF dist sides) / 2 := by positivity
  have hF : ∀ᶠ x in 𝓝 (displayCF dist sides), F (displayCF dist sides) / 2 < F x :=
    hcont.tendsto.eventually_const_lt (by linarith)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_iidProb_stat_gt hd F hhom hF (eventually_le_mul hb hd2))
  rw [hval, gt_iff_lt]
  exact Real.exp_lt_exp.2 (by linarith)

/-- Under the alternative of the T1 test, its statistic grows faster than any `b_n = o(n)`, so its
p-value is eventually below `exp(-b_n/2)`. -/
theorem t1PValue_growth (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (h : ¬ ((∀ r ∈ s.alternatives, displayCF dist sides r ≤ displayCF dist sides s) ∧
      ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
        displayCF dist sides r = displayCF dist sides r')) {b : ℕ → ℝ}
    (hb : Tendsto (fun n => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      t1PValue (quartetCount sides ω) s < Real.exp (-(b n) / 2)) atTop (𝓝 1) := by
  have hp0 : ∀ r, 0 ≤ displayCF dist sides r := displayCF_nonneg hd
  have hp1 := sum_displayCF_treesOn hd hs s.card_taxa
  obtain ⟨r, r', hne, halts⟩ := QuartetTree.exists_alternatives s
  have hr : r ∈ s.alternatives := by simp [halts]
  have hr' : r' ∈ s.alternatives := by simp [halts]
  have hrT := mem_treesOn_taxa_of_mem_alternatives hr
  have hrT' := mem_treesOn_taxa_of_mem_alternatives hr'
  have hsT := mem_treesOn_taxa s
  obtain ⟨d, hd0, hF⟩ : ∃ d : ℝ, 0 < d ∧ ∀ᶠ x in 𝓝 (displayCF dist sides), d < t1Stat x s := by
    by_cases heq : displayCF dist sides r = displayCF dist sides r'
    · -- on the line: the true topology has probability below the alternatives, in the star regime
      have hlt : displayCF dist sides s < displayCF dist sides r := by
        by_contra hcon
        push Not at hcon
        refine h ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩
        · rw [halts] at hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hcon
          · rw [← heq]; exact hcon
        · rw [halts] at hu hu'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
          rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
          · rfl
          · exact heq
          · exact heq.symm
          · rfl
      have hstar : 0 < starStat (displayCF dist sides) s.taxa := by
        refine starStat_pos _ hp0 s.card_taxa hp1 ?_
        by_cases hs3 : displayCF dist sides s = 1 / 3
        · exact ⟨r, hrT, fun h' => by linarith⟩
        · exact ⟨s, hsT, hs3⟩
      refine ⟨starStat (displayCF dist sides) s.taxa / 2, by positivity, ?_⟩
      have h1 : ∀ᶠ x in 𝓝 (displayCF dist sides),
          starStat (displayCF dist sides) s.taxa / 2 < starStat x s.taxa :=
        (continuous_starStat s.taxa).continuousAt.tendsto.eventually_const_lt (by linarith)
      have h2 : ∀ᶠ x : QuartetTree X → ℝ in 𝓝 (displayCF dist sides),
          x s < (x r + x r') / 2 := by
        refine ContinuousAt.eventually_lt (continuous_apply s).continuousAt
          (((continuous_apply r).add (continuous_apply r')).div_const 2).continuousAt ?_
        rw [← heq]
        linarith
      filter_upwards [h1, h2] with x hx1 hx2
      unfold t1Stat
      rw [halts, Finset.sum_pair hne, ite_eq_right (not_le.2 hx2)]
      exact hx1
    · -- off the line: both statistics of the T1 test are positive
      have hline : 0 < lineStat (displayCF dist sides) s :=
        lineStat_pos _ hp0 s ⟨r, hr, r', hr', heq⟩
      have hstar : 0 < starStat (displayCF dist sides) s.taxa := by
        refine starStat_pos _ hp0 s.card_taxa hp1 ?_
        by_cases hs3 : displayCF dist sides r = 1 / 3
        · exact ⟨r', hrT', fun h' => heq (hs3.trans h'.symm)⟩
        · exact ⟨r, hrT, hs3⟩
      refine ⟨min (lineStat (displayCF dist sides) s) (starStat (displayCF dist sides) s.taxa) / 2,
        by positivity, ?_⟩
      have hmin : 0 < min (lineStat (displayCF dist sides) s)
          (starStat (displayCF dist sides) s.taxa) := lt_min hline hstar
      have h1 : ∀ᶠ x in 𝓝 (displayCF dist sides),
          min (lineStat (displayCF dist sides) s) (starStat (displayCF dist sides) s.taxa) / 2 <
            lineStat x s :=
        (continuous_lineStat s).continuousAt.tendsto.eventually_const_lt
          (by have := min_le_left (lineStat (displayCF dist sides) s)
                (starStat (displayCF dist sides) s.taxa); linarith)
      have h2 : ∀ᶠ x in 𝓝 (displayCF dist sides),
          min (lineStat (displayCF dist sides) s) (starStat (displayCF dist sides) s.taxa) / 2 <
            starStat x s.taxa :=
        (continuous_starStat s.taxa).continuousAt.tendsto.eventually_const_lt
          (by have := min_le_right (lineStat (displayCF dist sides) s)
                (starStat (displayCF dist sides) s.taxa); linarith)
      filter_upwards [h1, h2] with x hx1 hx2
      unfold t1Stat
      split_ifs
      · exact hx1
      · exact hx2
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_iidProb_stat_gt hd (fun c => t1Stat c s) (fun a ha c => t1Stat_const_mul ha c s) hF
      (eventually_le_mul hb hd0))
  have hc := quartetCount_nonneg (sides := sides) ω
  have hmu := muZero_t1Phi_nonneg (quartetCount sides ω) s
  have hstat := t1Stat_nonneg (quartetCount sides ω) hc s
  calc t1PValue (quartetCount sides ω) s ≤ chiSqTwoTail (t1Stat (quartetCount sides ω) s) :=
        t1Tail_le_chiSqTwoTail hmu hstat
    _ < _ := Real.exp_lt_exp.2 (by linarith)

/-- The upper tail of `χ²₁` tends to zero, and not exponentially fast. -/
theorem tendsto_chiSqOneTail_log : Tendsto (fun n : ℕ => chiSqOneTail (Real.log n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ => chiSqTwoTail (Real.log n)) atTop (𝓝 0) := by
    unfold chiSqTwoTail
    refine Real.tendsto_exp_atBot.comp ?_
    have : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop := hlog.atTop_div_const (by norm_num)
    refine (tendsto_neg_atTop_atBot.comp this).congr fun n => ?_
    simp only [Function.comp]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (Eventually.of_forall fun n => chiSqOneTail_nonneg _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact chiSqOneTail_le_chiSqTwoTail (Real.log_natCast_nonneg n)

theorem chiSqOneTail_log_pos : ∀ᶠ n : ℕ in atTop, 0 < chiSqOneTail (Real.log n) :=
  Eventually.of_forall fun _ => chiSqOneTail_pos _

/-- A lower bound for the logarithm of the tail of `χ²₁`. -/
private lemma log_chiSqOneTail_ge {t : ℝ} (ht : 0 ≤ t) :
    -Real.log (√(2 * Real.pi)) - 1 - t ≤ Real.log (chiSqOneTail t) := by
  have h1 := gaussianPDFReal_le_chiSqOneTail t
  have h2 := Real.log_le_log (gaussianPDFReal_pos _ _ _ one_ne_zero) h1
  refine le_trans ?_ h2
  have hpi : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.log_mul (inv_ne_zero hpi.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  have h3 : √t ^ 2 = t := Real.sq_sqrt ht
  nlinarith [sq_nonneg (√t - 1)]

theorem tendsto_log_chiSqOneTail_log :
    Tendsto (fun n : ℕ => Real.log (chiSqOneTail (Real.log n)) / n) atTop (𝓝 0) := by
  set C := -Real.log (√(2 * Real.pi)) - 1 with hC
  have hlow : Tendsto (fun n : ℕ => (C - Real.log n) / n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop C
    have h2 : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
      have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using this
    have := h1.sub h2
    simp only [sub_zero] at this
    refine this.congr fun n => ?_
    exact (sub_div _ _ _).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := log_chiSqOneTail_ge (Real.log_natCast_nonneg n)
    exact div_le_div_of_nonneg_right (by linarith) hn'.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos (chiSqOneTail_nonneg _) (chiSqOneTail_le_one _)) hn'.le

/-- `β_n = 1/√n`. -/
theorem chiSqTwoTail_log (n : ℕ) (hn : 0 < n) :
    chiSqTwoTail (Real.log n) = 1 / Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold chiSqTwoTail
  rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hn', one_div]

/-- The cut test on a non-cut, positive concordance factor: for each `b_n = o(n)`, whatever the fitted
line, the p-value is eventually below the `χ²₁` tail at `b_n`, by the domination of the test
distribution by `Z²`. (TINNiK's proof of Theorem 4, repaired: E10 of the report.) -/
theorem cutTest_alternative (hd : IsDist dist) {q : Finset X}
    (hq : q.card = 4) (hnc : ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, r ≠ r' →
      displayCF dist sides r ≠ displayCF dist sides r') :
    ∃ d : ℝ, 0 < d ∧ Tendsto (fun n : ℕ => iidProb dist n fun ω =>
      ∀ s ∈ treesOn q, cutPValue (quartetCount sides ω) s < chiSqOneTail (n * d)) atTop (𝓝 1) := by
  have hp0 : ∀ r, 0 ≤ displayCF dist sides r := displayCF_nonneg hd
  have htaxa : ∀ s ∈ treesOn q, s.taxa = q := fun s hs => (Finset.mem_filter.1 hs).2
  have hpos : ∀ s ∈ treesOn q, 0 < lineStat (displayCF dist sides) s := by
    intro s hsq
    obtain ⟨r, r', hne, halts⟩ := QuartetTree.exists_alternatives s
    have hr : r ∈ s.alternatives := by simp [halts]
    have hr' : r' ∈ s.alternatives := by simp [halts]
    have hrT := mem_treesOn_taxa_of_mem_alternatives hr
    have hrT' := mem_treesOn_taxa_of_mem_alternatives hr'
    rw [htaxa s hsq] at hrT hrT'
    exact lineStat_pos _ hp0 s ⟨r, hr, r', hr', hnc r hrT r' hrT' hne⟩
  have hne : (treesOn q).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq]
    norm_num
  obtain ⟨s₀, hs₀, hmin⟩ := Finset.exists_min_image _ (lineStat (displayCF dist sides)) hne
  have hd0 : 0 < lineStat (displayCF dist sides) s₀ / 2 := by
    have := hpos s₀ hs₀
    positivity
  refine ⟨lineStat (displayCF dist sides) s₀ / 2, hd0, ?_⟩
  set d := lineStat (displayCF dist sides) s₀ / 2 with hd_def
  have hF : ∀ᶠ x in 𝓝 (displayCF dist sides), ∀ s ∈ treesOn q, d < lineStat x s := by
    rw [Finset.eventually_all]
    intro s hsq
    refine (continuous_lineStat s).continuousAt.tendsto.eventually_const_lt ?_
    have := hmin s hsq
    have := hpos s₀ hs₀
    linarith
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_iidProb_freq hd hF)
  filter_upwards [eventually_gt_atTop 0] with n hn0 ω hω s hsq
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc : quartetCount sides ω = fun r => (n : ℝ) * (quartetCount sides ω r / n) := by
    funext r
    field_simp
  have hline : ∀ u ∈ treesOn q, (n : ℝ) * d < lineStat (quartetCount sides ω) u := by
    intro u hu
    rw [hc, lineStat_const_mul hn'.ne']
    exact mul_lt_mul_of_pos_left (hω u hu) hn'
  have hcut : (n : ℝ) * d < cutStat (quartetCount sides ω) q := by
    have : Nonempty {s // s ∈ treesOn q} := ⟨⟨s₀, hs₀⟩⟩
    obtain ⟨u, hu⟩ := exists_eq_ciInf_of_finite
      (f := fun u : {s // s ∈ treesOn q} => lineStat (quartetCount sides ω) u.val)
    unfold cutStat
    rw [← hu]
    exact hline u.val u.property
  unfold cutPValue
  rw [htaxa s hsq]
  exact (cutTail_le_chiSqOneTail _ _ _).trans_lt
    (chiSqOneTail_lt_of_lt (by positivity) hcut)

end Phylogenetics.QuartetTests
