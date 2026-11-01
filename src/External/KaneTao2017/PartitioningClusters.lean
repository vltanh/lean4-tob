module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kane and Tao 2017: a bound on partitioning clusters

D. Kane, T. Tao, *A bound on partitioning clusters*, Electron. J. Combin. 24 (2017), P2.31, read in its arXiv TeX (1702.00912v2). Its Theorem 1:
for a finite collection `X` of sets, the number of `(A₁, A₂, A) ∈ X³` with `A` the disjoint union of `A₁` and `A₂` is at most `|X|^(3/p)`, with
`p = log₃(27/4) = 1.73814...`, so `3/p = 1.72598...`. This is the `1.726` of the running time of ASTRAL-III that TOB-QMC quotes.

As in the source, this comes from a one-dimensional inequality, its (abc), by induction on the dimension: `elementary_inequality`, `card_triples_le`,
`theorem1`. The source tensorizes a convolution estimate for functions on `{0,1}ⁿ`, one block of coordinates at a time. Here the
induction is on one taxon at a time, for three families of sets, which is the form of its second remark; no functions are needed.

Departure from the source, for (abc). The source proves it by compactness: the inequality near the boundary by concavity and continuity, for
an unspecified small `ε`, and in the interior at the critical points of a function of three variables, one of which is a root of
`u = 1 + (u/2)^(1/(p-1))`, found numerically, at which the function is checked numerically to be positive. Here (abc) is instead reduced to
a separable inequality in one probability vector:

* (abc) follows from `∑ ψ(π_i) ≥ 0` on the simplex (`sum_psi_nonneg`), with `ψ(t) = (p-1) t log t - (1-t) log(1-t)`, by Gibbs' inequality. In terms of entropy
  this reads `p H(π) ≤ h(π₁) + h(π₂) + h(π₃)`. The function `ψ` vanishes at `0`, `1/3` and `1`, which are the four cases of equality in the source;
* `ψ` is convex on `[0, (p-1)/p]`, so when the two smaller entries lie there, they can be taken equal (`psi_add_psi_ge`). What remains is one variable, `g(ε) =
  ψ(1-2ε) + 2ψ(ε)`, whose second derivative has the sign of the linear function `(p-2) + (3-p)ε`. So `g` is concave and then convex, with `g(0) = 0` and a
  double zero at `1/3`, so it is nonnegative with no numerical check (`g_nonneg`);
* when the second entry passes `(p-1)/p`, the sum is far from zero, and bounds on `log 2`, `log 3` suffice (`sum_psi_nonneg_of_large`).

That the exponent cannot be improved, the second sentence of the source's Theorem 1, is not formalized: TOB-QMC and ASTRAL-III use only the upper bound. The reduction in the source
to finite sets is not needed: sets here are `Finset α`.
-/

@[expose] public noncomputable section

open Real Finset

namespace External.KaneTao2017

/-! ### The constants -/

/-- The exponent `p = log₃(27/4)`. -/
def p : ℝ := Real.log (27 / 4) / Real.log 3

/-- `q = p - 1`. -/
def q : ℝ := p - 1

theorem log_three_gt : (1.0986 : ℝ) < Real.log 3 := by
  have h2 := Real.log_two_gt_d9
  have hr : (0 : ℝ) < 524288 / 531441 := by norm_num
  have h := Real.log_le_sub_one_of_pos hr
  have he : Real.log (524288 / 531441) = 19 * Real.log 2 - 12 * Real.log 3 := by
    rw [show (524288 : ℝ) = 2 ^ 19 by norm_num, show (531441 : ℝ) = 3 ^ 12 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [he] at h
  norm_num at h h2 ⊢
  linarith

theorem log_three_lt : Real.log 3 < (1.09863 : ℝ) := by
  have h2 := Real.log_two_lt_d9
  have hr : (0 : ℝ) < 531441 / 524288 := by norm_num
  have h := Real.log_le_sub_one_of_pos hr
  have he : Real.log (531441 / 524288) = 12 * Real.log 3 - 19 * Real.log 2 := by
    rw [show (524288 : ℝ) = 2 ^ 19 by norm_num, show (531441 : ℝ) = 3 ^ 12 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [he] at h
  norm_num at h h2 ⊢
  linarith

theorem log_three_pos : 0 < Real.log 3 := lt_trans (by norm_num) log_three_gt

theorem log_twentyseven_quarters : Real.log (27 / 4) = 3 * Real.log 3 - 2 * Real.log 2 := by
  rw [show (27 : ℝ) = 3 ^ 3 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num

theorem q_mul_log_three : q * Real.log 3 = 2 * Real.log 3 - 2 * Real.log 2 := by
  have h3 := log_three_pos
  unfold q p
  rw [log_twentyseven_quarters]
  field_simp
  ring

theorem q_ge : (0.738125 : ℝ) ≤ q := by
  have h := q_mul_log_three
  have h2 := Real.log_two_lt_d9
  have h3 := log_three_gt
  by_contra hlt
  push Not at hlt
  have : q * Real.log 3 < 0.738125 * Real.log 3 := mul_lt_mul_of_pos_right hlt log_three_pos
  norm_num at this h2 h3
  linarith

theorem q_le : q ≤ (0.7382 : ℝ) := by
  have h := q_mul_log_three
  have h2 := Real.log_two_gt_d9
  have h3 := log_three_lt
  by_contra hlt
  push Not at hlt
  have : 0.7382 * Real.log 3 < q * Real.log 3 := mul_lt_mul_of_pos_right hlt log_three_pos
  norm_num at this h2 h3
  linarith

theorem q_pos : 0 < q := lt_of_lt_of_le (by norm_num) q_ge

theorem q_lt_one : q < 1 := lt_of_le_of_lt q_le (by norm_num)

theorem p_eq : p = q + 1 := by
  unfold q
  ring

theorem p_pos : 0 < p := by
  rw [p_eq]
  linarith [q_pos]

/-- **`3/p = 1.72598...` is at most the `1.726` that ASTRAL-III prints.** -/
theorem three_div_p_le : 3 / p ≤ (1.726 : ℝ) := by
  rw [div_le_iff₀ p_pos, p_eq]
  have := q_ge
  norm_num at this ⊢
  linarith

/-- `3/p` is above `1.7259`: the printed `1.726` is close. -/
theorem three_div_p_gt : (1.7259 : ℝ) < 3 / p := by
  rw [lt_div_iff₀ p_pos, p_eq]
  have := q_le
  norm_num at this ⊢
  linarith

/-! ### The function `ψ` -/

/-- `ψ(t) = (p-1) t log t - (1-t) log(1-t)`. -/
def psi (t : ℝ) : ℝ := negMulLog (1 - t) - q * negMulLog t

theorem psi_zero : psi 0 = 0 := by simp [psi]

theorem psi_one : psi 1 = 0 := by simp [psi]

theorem psi_one_third : psi (1 / 3) = 0 := by
  have h := q_mul_log_three
  have h₁ : Real.log (1 / 3) = - Real.log 3 := by
    rw [one_div, Real.log_inv]
  have h₂ : Real.log (2 / 3) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  simp only [psi, negMulLog]
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, h₁, h₂]
  linarith

theorem continuous_psi : Continuous psi := by
  unfold psi
  exact (continuous_negMulLog.comp (continuous_const.sub continuous_id)).sub
    (continuous_const.mul continuous_negMulLog)

/-- The derivative of `ψ`. -/
def dpsi (t : ℝ) : ℝ := q * Real.log t + q + Real.log (1 - t) + 1

theorem hasDerivAt_psi {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1) : HasDerivAt psi (dpsi t) t := by
  have hin : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h₁ : HasDerivAt (fun t => negMulLog (1 - t)) ((- Real.log (1 - t) - 1) * (-1)) t :=
    (hasDerivAt_negMulLog (sub_ne_zero.2 h1.symm)).comp t hin
  have h₂ := (hasDerivAt_negMulLog h0).const_mul q
  change HasDerivAt (fun t => negMulLog (1 - t) - q * negMulLog t) (dpsi t) t
  refine (h₁.fun_sub h₂).congr_deriv ?_
  unfold dpsi
  ring

theorem hasDerivAt_dpsi {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : HasDerivAt dpsi (q / t - 1 / (1 - t)) t := by
  have h₁ := (Real.hasDerivAt_log h0.ne').const_mul q
  have hin : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h₂ := hin.log (sub_pos.2 h1).ne'
  change HasDerivAt (fun t => q * Real.log t + q + Real.log (1 - t) + 1) _ t
  refine (((h₁.add_const q).fun_add h₂).add_const 1).congr_deriv ?_
  have h1t : 1 - t ≠ 0 := (sub_pos.2 h1).ne'
  field_simp
  ring

/-- The point up to which `ψ` is convex. -/
def tau : ℝ := q / (1 + q)

theorem tau_pos : 0 < tau := div_pos q_pos (by linarith [q_pos])

theorem tau_lt_one : tau < 1 := by
  rw [tau, div_lt_one (by linarith [q_pos])]
  linarith

/-- **`ψ` is convex up to `(p-1)/p`.** -/
theorem convexOn_psi : ConvexOn ℝ (Set.Icc 0 tau) psi := by
  have hsub : ∀ {t : ℝ}, t ∈ Set.Ioo 0 tau → t ≠ 0 ∧ t ≠ 1 := fun ht =>
    ⟨ht.1.ne', (ht.2.trans tau_lt_one).ne⟩
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) continuous_psi.continuousOn ?_ ?_
  · rw [interior_Icc]
    exact fun t ht => (hasDerivAt_psi (hsub ht).1 (hsub ht).2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    have hmono : MonotoneOn dpsi (Set.Ioo 0 tau) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
      · exact fun t ht => (hasDerivAt_dpsi ht.1 (ht.2.trans tau_lt_one)).continuousAt.continuousWithinAt
      · rw [interior_Ioo]
        exact fun t ht => (hasDerivAt_dpsi ht.1 (ht.2.trans tau_lt_one)).differentiableAt.differentiableWithinAt
      · rw [interior_Ioo]
        intro t ht
        rw [(hasDerivAt_dpsi ht.1 (ht.2.trans tau_lt_one)).deriv]
        have h1t : 0 < 1 - t := sub_pos.2 (ht.2.trans tau_lt_one)
        have hq1 : 0 < 1 + q := by linarith [q_pos]
        have hle : t * (1 + q) ≤ q := by
          have := (lt_div_iff₀ hq1).1 ht.2
          exact this.le
        rw [sub_nonneg, div_le_div_iff₀ h1t ht.1]
        nlinarith
    intro x hx y hy hxy
    rw [(hasDerivAt_psi (hsub hx).1 (hsub hx).2).deriv, (hasDerivAt_psi (hsub hy).1 (hsub hy).2).deriv]
    exact hmono hx hy hxy

/-! ### The line -/

/-- `ψ` on the line of two equal entries. -/
def g (ε : ℝ) : ℝ := psi (1 - 2 * ε) + 2 * psi ε

theorem g_zero : g 0 = 0 := by
  simp [g, psi_zero, psi_one]

theorem g_one_third : g (1 / 3) = 0 := by
  rw [g, show (1 : ℝ) - 2 * (1 / 3) = 1 / 3 by norm_num, psi_one_third]
  norm_num

theorem continuous_g : Continuous g := by
  unfold g
  exact (continuous_psi.comp (continuous_const.sub (continuous_const.mul continuous_id))).add
    (continuous_const.mul continuous_psi)

/-- Half the derivative of `g`. -/
def dg (ε : ℝ) : ℝ := (q - 1) * Real.log ε + Real.log (1 - ε) - q * Real.log (1 - 2 * ε) - Real.log 2

theorem hasDerivAt_g {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) : HasDerivAt g (2 * dg ε) ε := by
  have hin : HasDerivAt (fun ε : ℝ => 1 - 2 * ε) (-2) ε := by
    simpa using ((hasDerivAt_id ε).const_mul 2).const_sub 1
  have hne0 : 1 - 2 * ε ≠ 0 := by
    intro h
    linarith
  have hne1 : 1 - 2 * ε ≠ 1 := by
    intro h
    linarith
  have h₀ := HasDerivAt.comp (h₂ := psi) ε (hasDerivAt_psi hne0 hne1) hin
  have h₁ : HasDerivAt (fun ε => psi (1 - 2 * ε)) (dpsi (1 - 2 * ε) * (-2)) ε := h₀
  have h₂ := (hasDerivAt_psi h0.ne' (by linarith : ε < 1).ne).const_mul 2
  have hlog : Real.log (1 - (1 - 2 * ε)) = Real.log 2 + Real.log ε := by
    rw [show (1 : ℝ) - (1 - 2 * ε) = 2 * ε by ring, Real.log_mul (by norm_num) h0.ne']
  change HasDerivAt (fun ε => psi (1 - 2 * ε) + 2 * psi ε) _ ε
  refine (h₁.fun_add h₂).congr_deriv ?_
  unfold dpsi dg
  rw [hlog]
  ring

theorem hasDerivAt_dg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    HasDerivAt dg (((q - 1) + (2 - q) * ε) / (ε * (1 - ε) * (1 - 2 * ε))) ε := by
  have h₁ := (Real.hasDerivAt_log h0.ne').const_mul (q - 1)
  have hin₁ : HasDerivAt (fun ε : ℝ => 1 - ε) (-1) ε := by
    simpa using (hasDerivAt_id ε).const_sub 1
  have hin₂ : HasDerivAt (fun ε : ℝ => 1 - 2 * ε) (-2) ε := by
    simpa using ((hasDerivAt_id ε).const_mul 2).const_sub 1
  have h1e : 1 - ε ≠ 0 := by
    intro h
    linarith
  have h2e : 1 - 2 * ε ≠ 0 := by
    intro h
    linarith
  have h₂ := hin₁.log h1e
  have h₃ := (hin₂.log h2e).const_mul q
  change HasDerivAt (fun ε => (q - 1) * Real.log ε + Real.log (1 - ε) - q * Real.log (1 - 2 * ε) - Real.log 2) _ ε
  refine (((h₁.fun_add h₂).fun_sub h₃).sub_const (Real.log 2)).congr_deriv ?_
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero h0.ne' h1e) h2e), div_eq_mul_inv (-1 : ℝ), div_eq_mul_inv (-2 : ℝ)]
  have ha := inv_mul_cancel₀ h0.ne'
  have hb := inv_mul_cancel₀ h1e
  have hc := inv_mul_cancel₀ h2e
  linear_combination (q - 1) * (1 - ε) * (1 - 2 * ε) * ha - ε * (1 - 2 * ε) * hb + 2 * q * ε * (1 - ε) * hc

theorem dg_one_third : dg (1 / 3) = 0 := by
  have h₁ : Real.log (1 / 3) = - Real.log 3 := by
    rw [one_div, Real.log_inv]
  have h₂ : Real.log (2 / 3) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  unfold dg
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show (1 : ℝ) - 2 * (1 / 3) = 1 / 3 by norm_num, h₁, h₂]
  ring

/-- Where the second derivative of `g` changes sign. -/
def eps0 : ℝ := (1 - q) / (2 - q)

theorem eps0_pos : 0 < eps0 := div_pos (sub_pos.2 q_lt_one) (by linarith [q_lt_one])

theorem eps0_lt : eps0 < 1 / 3 := by
  have := q_ge
  rw [eps0, div_lt_iff₀ (by linarith [q_lt_one])]
  norm_num at this ⊢
  linarith

/-- The sign of the second derivative of `g`. -/
theorem numerator_nonneg_iff {ε : ℝ} : 0 ≤ (q - 1) + (2 - q) * ε ↔ eps0 ≤ ε := by
  have h2q : 0 < 2 - q := by linarith [q_lt_one]
  rw [eps0, div_le_iff₀ h2q]
  constructor <;> intro h <;> nlinarith

/-- On `[eps0, 1/3]`, `g` decreases to its zero at `1/3`: it is convex there, with a critical point at `1/3`. -/
theorem g_nonneg_of_ge {ε : ℝ} (h0 : eps0 ≤ ε) (h1 : ε ≤ 1 / 3) : 0 ≤ g ε := by
  have hε : ∀ {t : ℝ}, t ∈ Set.Icc eps0 (1 / 3) → 0 < t ∧ t < 1 / 2 := fun ht =>
    ⟨eps0_pos.trans_le ht.1, ht.2.trans_lt (by norm_num)⟩
  have hmono : MonotoneOn dg (Set.Icc eps0 (1 / 3)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun t ht => (hasDerivAt_dg (hε ht).1 (hε ht).2).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => (hasDerivAt_dg (hε (Set.Ioo_subset_Icc_self ht)).1
        (hε (Set.Ioo_subset_Icc_self ht)).2).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨ht0, ht1⟩ := hε (Set.Ioo_subset_Icc_self ht)
      rw [(hasDerivAt_dg ht0 ht1).deriv]
      refine div_nonneg (numerator_nonneg_iff.2 ht.1.le) ?_
      exact mul_nonneg (mul_nonneg ht0.le (by linarith)) (by linarith)
  have hdg : ∀ t ∈ Set.Icc eps0 (1 / 3 : ℝ), dg t ≤ 0 := fun t ht => by
    rw [← dg_one_third]
    exact hmono ht ⟨eps0_lt.le, le_rfl⟩ ht.2
  have hanti : AntitoneOn g (Set.Icc eps0 (1 / 3)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) continuous_g.continuousOn ?_ ?_
    · rw [interior_Icc]
      exact fun t ht => (hasDerivAt_g (hε (Set.Ioo_subset_Icc_self ht)).1
        (hε (Set.Ioo_subset_Icc_self ht)).2).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨ht0, ht1⟩ := hε (Set.Ioo_subset_Icc_self ht)
      rw [(hasDerivAt_g ht0 ht1).deriv]
      have := hdg t (Set.Ioo_subset_Icc_self ht)
      linarith
  have := hanti ⟨h0, h1⟩ ⟨eps0_lt.le, le_rfl⟩ h1
  rwa [g_one_third] at this

/-- **`g` is concave on `[0, eps0]`.** -/
theorem concaveOn_g : ConcaveOn ℝ (Set.Icc 0 eps0) g := by
  have hε : ∀ {t : ℝ}, t ∈ Set.Ioo 0 eps0 → 0 < t ∧ t < 1 / 2 := fun ht =>
    ⟨ht.1, ht.2.trans (eps0_lt.trans (by norm_num))⟩
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) continuous_g.continuousOn ?_ ?_
  · rw [interior_Icc]
    exact fun t ht => (hasDerivAt_g (hε ht).1 (hε ht).2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    have hanti : AntitoneOn dg (Set.Ioo 0 eps0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioo _ _) ?_ ?_ ?_
      · exact fun t ht => (hasDerivAt_dg (hε ht).1 (hε ht).2).continuousAt.continuousWithinAt
      · rw [interior_Ioo]
        exact fun t ht => (hasDerivAt_dg (hε ht).1 (hε ht).2).differentiableAt.differentiableWithinAt
      · rw [interior_Ioo]
        intro t ht
        obtain ⟨ht0, ht1⟩ := hε ht
        rw [(hasDerivAt_dg ht0 ht1).deriv]
        have hneg : (q - 1) + (2 - q) * t ≤ 0 := by
          by_contra hcon
          exact absurd ht.2 (not_lt.2 (numerator_nonneg_iff.1 (not_le.1 hcon).le))
        refine div_nonpos_of_nonpos_of_nonneg hneg ?_
        exact mul_nonneg (mul_nonneg ht0.le (by linarith)) (by linarith)
    intro x hx y hy hxy
    rw [(hasDerivAt_g (hε hx).1 (hε hx).2).deriv, (hasDerivAt_g (hε hy).1 (hε hy).2).deriv]
    have := hanti hx hy hxy
    linarith

/-- **`g ≥ 0` on `[0, 1/3]`**, with no numerical check: `g` is concave and then convex, with `g(0) = 0` and a double zero at `1/3`. -/
theorem g_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 3) : 0 ≤ g ε := by
  by_cases h : eps0 ≤ ε
  · exact g_nonneg_of_ge h h1
  · have hlt := not_le.1 h
    have hend : 0 ≤ g eps0 := g_nonneg_of_ge le_rfl eps0_lt.le
    have hb : ε / eps0 ≤ 1 := (div_le_one eps0_pos).2 hlt.le
    have hb₀ : 0 ≤ ε / eps0 := div_nonneg h0 eps0_pos.le
    have hc := concaveOn_g.2 (Set.left_mem_Icc.2 eps0_pos.le) (Set.right_mem_Icc.2 eps0_pos.le)
      (sub_nonneg.2 hb) hb₀ (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hc
    rw [div_mul_cancel₀ _ eps0_pos.ne', g_zero] at hc
    have := mul_nonneg hb₀ hend
    linarith

/-! ### The simplex -/

/-- When the two smaller entries are in the range where `ψ` is convex, they can be taken equal. -/
theorem sum_psi_nonneg_of_small {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b + c = 1) (hac : a ≤ c) (hbc : b ≤ c)
    (haτ : a ≤ tau) (hbτ : b ≤ tau) : 0 ≤ psi a + psi b + psi c := by
  have hconv := convexOn_psi.2 (show a ∈ Set.Icc 0 tau from ⟨ha, haτ⟩) (show b ∈ Set.Icc 0 tau from ⟨hb, hbτ⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hconv
  have hg := g_nonneg (ε := (a + b) / 2) (by linarith) (by linarith)
  rw [g, show 1 - 2 * ((a + b) / 2) = c by linarith, show (a + b) / 2 = 1 / 2 * a + 1 / 2 * b by ring] at hg
  linarith

/-- `log (1 - x) ≤ - x - x² / 2`. -/
theorem log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Real.log (1 - x) ≤ - x - x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => Real.log (1 - x) + x + x ^ 2 / 2
  have hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivAt f (- t ^ 2 / (1 - t)) t := by
    intro t ht
    have hne : 1 - t ≠ 0 := (sub_pos.2 ht.2).ne'
    have hin : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hp : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
      have := ((hasDerivAt_id t).pow 2).div_const 2
      simpa using this
    refine (((hin.log hne).fun_add (hasDerivAt_id t)).fun_add hp).congr_deriv ?_
    field_simp
    ring
  have hanti : AntitoneOn f (Set.Ico 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico _ _) ?_ ?_ ?_
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · rw [interior_Ico]
      exact fun t ht => (hder t (Set.Ioo_subset_Ico_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro t ht
      rw [(hder t (Set.Ioo_subset_Ico_self ht)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg t]) (sub_pos.2 ht.2).le
  have h := hanti ⟨le_rfl, zero_lt_one⟩ ⟨h0, h1⟩ h0
  simp only [f] at h
  norm_num at h
  linarith

/-- A lower bound on `ψ` near `1/2`, by `log x ≤ x - 1` at `2 t` and `2 (1 - t)`. -/
theorem psi_ge_mid {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    q * (t - 1 / 2 - t * Real.log 2) + (1 - t) * (Real.log 2 + 2 * t - 1) ≤ psi t := by
  have h1t : 0 < 1 - t := sub_pos.2 h1
  have hq := q_pos
  -- `t log t ≥ t - 1/2 - t log 2`
  have ha : t - 1 / 2 - t * Real.log 2 ≤ t * Real.log t := by
    have hx : 0 < 1 / (2 * t) := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) h0.ne'] at h
    have hm := mul_le_mul_of_nonneg_left h h0.le
    have hc : t * ((2 * t)⁻¹ - 1) = 1 / 2 - t := by
      field_simp
    rw [hc] at hm
    nlinarith
  -- `log (1 - t) ≤ 1 - 2 t - log 2`
  have hb : Real.log (1 - t) ≤ 1 - 2 * t - Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * (1 - t))
    rw [Real.log_mul (by norm_num) h1t.ne'] at h
    linarith
  have hb' := mul_le_mul_of_nonneg_left hb h1t.le
  have ha' := mul_le_mul_of_nonneg_left ha hq.le
  simp only [psi, negMulLog]
  nlinarith

/-- A lower bound on `ψ` near its minimum, by `log x ≤ x - 1` at `8 a` and `log_one_sub_le`. -/
theorem psi_ge_small {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) :
    q * (a * (1 - 3 * Real.log 2) - 1 / 8) + a - a ^ 2 / 2 - a ^ 3 / 2 ≤ psi a := by
  have h1a : 0 < 1 - a := sub_pos.2 h1
  have hq := q_pos
  have ha : a * (1 - 3 * Real.log 2) - 1 / 8 ≤ a * Real.log a := by
    rcases h0.eq_or_lt with h | h
    · rw [← h]
      norm_num
    · have hx : 0 < 1 / (8 * a) := by positivity
      have hl := Real.log_le_sub_one_of_pos hx
      have h8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      rw [one_div, Real.log_inv, Real.log_mul (by norm_num) h.ne', h8] at hl
      have hm := mul_le_mul_of_nonneg_left hl h.le
      have hc : a * ((8 * a)⁻¹ - 1) = 1 / 8 - a := by
        field_simp
      rw [hc] at hm
      nlinarith
  have hb := mul_le_mul_of_nonneg_left (log_one_sub_le h0 h1) h1a.le
  have ha' := mul_le_mul_of_nonneg_left ha hq.le
  simp only [psi, negMulLog]
  nlinarith

/-- When the second entry is past the range where `ψ` is convex, the sum is well above zero. -/
theorem sum_psi_nonneg_of_large {a b c : ℝ} (ha : 0 ≤ a) (hsum : a + b + c = 1) (hbc : b ≤ c) (hb : tau < b) :
    0 ≤ psi a + psi b + psi c := by
  have hq₁ := q_ge
  have hq₂ := q_le
  have hL₁ := Real.log_two_gt_d9
  have hL₂ := Real.log_two_lt_d9
  norm_num at hq₁ hq₂ hL₁ hL₂
  have hτ : (0.424 : ℝ) < tau := by
    rw [tau, lt_div_iff₀ (by linarith)]
    norm_num
    linarith
  norm_num at hτ
  have hb' : 53 / 125 < b := hτ.trans hb
  have hc' : 53 / 125 < c := hb'.trans_le hbc
  have ha₁ : a < 19 / 125 := by linarith
  have hb₁ : b < 72 / 125 := by linarith
  have hc₁ : c < 72 / 125 := by linarith
  have h₁ := psi_ge_small ha (by linarith : a < 1)
  have h₂ := psi_ge_mid (by linarith : 0 < b) (by linarith : b < 1)
  have h₃ := psi_ge_mid (by linarith : 0 < c) (by linarith : c < 1)
  set L := Real.log 2 with hL
  have hasub : a = 1 - b - c := by linarith
  have hkey : q * (a * (1 - 3 * L) - 1 / 8) + a - a ^ 2 / 2 - a ^ 3 / 2 +
      (q * (b - 1 / 2 - b * L) + (1 - b) * (L + 2 * b - 1)) +
      (q * (c - 1 / 2 - c * L) + (1 - c) * (L + 2 * c - 1)) =
      (1 - q) * L - q / 8 - a * (L * (2 * q - 1)) - 2 * ((b - 1 / 2) ^ 2 + (c - 1 / 2) ^ 2) - a ^ 2 / 2 - a ^ 3 / 2 := by
    rw [hasub]
    ring
  have e₁ : (181 / 1000 : ℝ) ≤ (1 - q) * L := by nlinarith
  have e₂ : L * (2 * q - 1) ≤ 331 / 1000 := by nlinarith
  have e₃ : a * (L * (2 * q - 1)) ≤ 19 / 125 * (331 / 1000) := by
    have hnn : 0 ≤ L * (2 * q - 1) := mul_nonneg (by linarith) (by linarith)
    exact mul_le_mul ha₁.le e₂ hnn (by norm_num)
  have e₄ : (b - 1 / 2) ^ 2 ≤ (19 / 250 : ℝ) ^ 2 := by
    apply sq_le_sq'  <;> linarith
  have e₅ : (c - 1 / 2) ^ 2 ≤ (19 / 250 : ℝ) ^ 2 := by
    apply sq_le_sq' <;> linarith
  have e₆ : a ^ 2 ≤ (19 / 125 : ℝ) ^ 2 := pow_le_pow_left₀ ha ha₁.le 2
  have e₇ : a ^ 3 ≤ (19 / 125 : ℝ) ^ 3 := pow_le_pow_left₀ ha ha₁.le 3
  norm_num at e₃ e₄ e₅ e₆ e₇
  linarith

/-- **The inequality on the simplex**: `ψ(a) + ψ(b) + ψ(c) ≥ 0` when `a, b, c ≥ 0` sum to one. In terms of entropy, `p H(a, b, c) ≤ h(a) + h(b) + h(c)`. Equality holds at
the centroid and the three vertices. -/
theorem sum_psi_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    0 ≤ psi a + psi b + psi c := by
  have sorted : ∀ {a b c : ℝ}, 0 ≤ a → 0 ≤ b → a + b + c = 1 → a ≤ b → b ≤ c → 0 ≤ psi a + psi b + psi c := by
    intro a b c ha hb hsum hab hbc
    by_cases hτ : b ≤ tau
    · exact sum_psi_nonneg_of_small ha hb hsum (hab.trans hbc) hbc (hab.trans hτ) hτ
    · exact sum_psi_nonneg_of_large ha hsum hbc (not_le.1 hτ)
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;> rcases le_total a c with hac | hac
  · exact sorted ha hb hsum hab hbc
  · exact sorted ha hb hsum hab hbc
  · linarith [sorted ha hc (by linarith : a + c + b = 1) hac hbc]
  · linarith [sorted hc ha (by linarith : c + a + b = 1) hac hab]
  · linarith [sorted hb ha (by linarith : b + a + c = 1) hab hac]
  · linarith [sorted hb hc (by linarith : b + c + a = 1) hbc hac]
  · linarith [sorted hc hb (by linarith : c + b + a = 1) hbc hab]
  · linarith [sorted hc hb (by linarith : c + b + a = 1) hbc hab]

/-! ### The inequality (abc) -/

/-- Gibbs' inequality for two outcomes, with Lean's `log 0 = 0` covering the boundary: if `x` puts mass where `y` does, `x log y + (1 - x) log (1 - y)` is at most
`- negMulLog x - negMulLog (1 - x)`. -/
theorem gibbs_two {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (h₁ : 0 < x → 0 < y) (h₂ : x < 1 → y < 1) :
    x * Real.log y + (1 - x) * Real.log (1 - y) ≤ - negMulLog x - negMulLog (1 - x) := by
  rcases hx0.eq_or_lt with h | hx
  · subst h
    have := Real.log_nonpos (sub_nonneg.2 hy1) (by linarith)
    simpa [negMulLog] using this
  rcases hx1.eq_or_lt with h | hx'
  · subst h
    have := Real.log_nonpos hy0 hy1
    simpa [negMulLog] using this
  have hy := h₁ hx
  have hy' := sub_pos.2 (h₂ hx')
  have h1x := sub_pos.2 hx'
  have key : ∀ {u v : ℝ}, 0 < u → 0 < v → u * Real.log v ≤ u * Real.log u + (v - u) := by
    intro u v hu hv
    have hlog := Real.log_le_sub_one_of_pos (div_pos hv hu)
    rw [Real.log_div hv.ne' hu.ne'] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog hu.le
    have hc : u * (v / u - 1) = v - u := by
      field_simp
    rw [hc] at hm
    linarith
  have ha := key hx hy
  have hb := key h1x hy'
  simp only [negMulLog]
  linarith

/-- **The inequality (abc) of the source** (`ext:kane_tao_abc`): for `0 ≤ a, b, c ≤ 1`, `(a b (1-c))^(1/p) + (b c (1-a))^(1/p) + (c a (1-b))^(1/p) ≤ 1`.

Departure from the source, as the head of this file says: Gibbs' inequality and `sum_psi_nonneg`, in place of a compactness argument and a numerically located critical point. Let `t₁, t₂, t₃` be
the three terms, `S` their sum, and `π_i = t_i / S`. Then `log S = H(π) + (1/p) ∑ π_i log m_i`, where `m_i` are the three products; collecting the logarithms of `a, 1-a`, and of `b`, `c`,
Gibbs' inequality gives `p log S ≤ p H(π) - ∑ h(π_i) = - ∑ ψ(π_i) ≤ 0`. -/
theorem elementary_inequality {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (a * b * (1 - c)) ^ (1 / p) + (b * c * (1 - a)) ^ (1 / p) + (c * a * (1 - b)) ^ (1 / p) ≤ 1 := by
  have hp := p_pos
  have hθ : 0 < 1 / p := one_div_pos.2 hp
  have h1a : 0 ≤ 1 - a := sub_nonneg.2 ha1
  have h1b : 0 ≤ 1 - b := sub_nonneg.2 hb1
  have h1c : 0 ≤ 1 - c := sub_nonneg.2 hc1
  set m₁ := a * b * (1 - c) with hm₁
  set m₂ := b * c * (1 - a) with hm₂
  set m₃ := c * a * (1 - b) with hm₃
  have hm₁0 : 0 ≤ m₁ := mul_nonneg (mul_nonneg ha0 hb0) h1c
  have hm₂0 : 0 ≤ m₂ := mul_nonneg (mul_nonneg hb0 hc0) h1a
  have hm₃0 : 0 ≤ m₃ := mul_nonneg (mul_nonneg hc0 ha0) h1b
  set t₁ := m₁ ^ (1 / p) with ht₁
  set t₂ := m₂ ^ (1 / p) with ht₂
  set t₃ := m₃ ^ (1 / p) with ht₃
  have ht₁0 : 0 ≤ t₁ := Real.rpow_nonneg hm₁0 _
  have ht₂0 : 0 ≤ t₂ := Real.rpow_nonneg hm₂0 _
  have ht₃0 : 0 ≤ t₃ := Real.rpow_nonneg hm₃0 _
  set S := t₁ + t₂ + t₃ with hS
  rcases (add_nonneg (add_nonneg ht₁0 ht₂0) ht₃0).eq_or_lt with hS0 | hSpos
  · rw [hS, ← hS0]
    exact zero_le_one
  set π₁ := t₁ / S with hπ₁
  set π₂ := t₂ / S with hπ₂
  set π₃ := t₃ / S with hπ₃
  have hπ₁0 : 0 ≤ π₁ := div_nonneg ht₁0 hSpos.le
  have hπ₂0 : 0 ≤ π₂ := div_nonneg ht₂0 hSpos.le
  have hπ₃0 : 0 ≤ π₃ := div_nonneg ht₃0 hSpos.le
  have hπsum : π₁ + π₂ + π₃ = 1 := by
    rw [hπ₁, hπ₂, hπ₃, ← add_div, ← add_div]
    exact div_self hSpos.ne'
  -- a positive term has positive factors
  have hpos₁ : 0 < π₁ → 0 < m₁ := fun h => by
    rcases hm₁0.eq_or_lt with h' | h'
    · have : t₁ = 0 := by rw [ht₁, ← h', Real.zero_rpow hθ.ne']
      simp [hπ₁, this] at h
    · exact h'
  have hpos₂ : 0 < π₂ → 0 < m₂ := fun h => by
    rcases hm₂0.eq_or_lt with h' | h'
    · have : t₂ = 0 := by rw [ht₂, ← h', Real.zero_rpow hθ.ne']
      simp [hπ₂, this] at h
    · exact h'
  have hpos₃ : 0 < π₃ → 0 < m₃ := fun h => by
    rcases hm₃0.eq_or_lt with h' | h'
    · have : t₃ = 0 := by rw [ht₃, ← h', Real.zero_rpow hθ.ne']
      simp [hπ₃, this] at h
    · exact h'
  have factors : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → 0 < x * y * z → 0 < x ∧ 0 < y ∧ z ≠ 0 := by
    intro x y z hx hy h
    have hz : z ≠ 0 := fun hz => by simp [hz] at h
    have hxy : x * y ≠ 0 := fun hxy => by simp [hxy] at h
    exact ⟨lt_of_le_of_ne hx (Ne.symm (left_ne_zero_of_mul hxy)),
      lt_of_le_of_ne hy (Ne.symm (right_ne_zero_of_mul hxy)), hz⟩
  -- the logarithm of `S`, term by term
  have hterm : ∀ {t m w x y z : ℝ}, t = m ^ (1 / p) → w = t / S → m = x * y * z → 0 ≤ m → 0 ≤ w →
      (0 < w → x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) →
      w * Real.log S = (1 / p) * (w * Real.log x + w * Real.log y + w * Real.log z) + negMulLog w := by
    intro t m w x y z ht hw hm hm0 hw0 hne
    rcases hw0.eq_or_lt with h | h
    · rw [← h]
      simp
    obtain ⟨hx, hy, hz⟩ := hne h
    have htpos : 0 < t := by
      rcases (Real.rpow_nonneg hm0 (1 / p)).eq_or_lt with h' | h'
      · rw [hw, ht, ← h'] at h
        simp at h
      · rwa [ht]
    have hmpos : 0 < m := by
      rcases hm0.eq_or_lt with h' | h'
      · exfalso
        rw [ht, ← h', Real.zero_rpow hθ.ne'] at htpos
        exact lt_irrefl _ htpos
      · exact h'
    have hlogt : Real.log t = (1 / p) * (Real.log x + Real.log y + Real.log z) := by
      rw [ht, Real.log_rpow hmpos, hm, Real.log_mul (mul_ne_zero hx hy) hz, Real.log_mul hx hy]
    have hlogw : Real.log w = Real.log t - Real.log S := by
      rw [hw, Real.log_div htpos.ne' hSpos.ne']
    simp only [negMulLog]
    rw [hlogw, hlogt]
    ring
  have ne₁ : 0 < π₁ → a ≠ 0 ∧ b ≠ 0 ∧ 1 - c ≠ 0 := fun h => by
    obtain ⟨hx, hy, hz⟩ := factors ha0 hb0 (hpos₁ h)
    exact ⟨hx.ne', hy.ne', hz⟩
  have ne₂ : 0 < π₂ → b ≠ 0 ∧ c ≠ 0 ∧ 1 - a ≠ 0 := fun h => by
    obtain ⟨hx, hy, hz⟩ := factors hb0 hc0 (hpos₂ h)
    exact ⟨hx.ne', hy.ne', hz⟩
  have ne₃ : 0 < π₃ → c ≠ 0 ∧ a ≠ 0 ∧ 1 - b ≠ 0 := fun h => by
    obtain ⟨hx, hy, hz⟩ := factors hc0 ha0 (hpos₃ h)
    exact ⟨hx.ne', hy.ne', hz⟩
  have e₁ := hterm ht₁ hπ₁ hm₁ hm₁0 hπ₁0 ne₁
  have e₂ := hterm ht₂ hπ₂ hm₂ hm₂0 hπ₂0 ne₂
  have e₃ := hterm ht₃ hπ₃ hm₃ hm₃0 hπ₃0 ne₃
  -- Gibbs' inequality for each of `a`, `b`, `c`
  have hπ₂1 : π₂ ≤ 1 := by linarith
  have hπ₃1 : π₃ ≤ 1 := by linarith
  have hπ₁1 : π₁ ≤ 1 := by linarith
  have ga : (1 - π₂) * Real.log a + π₂ * Real.log (1 - a) ≤ - negMulLog π₂ - negMulLog (1 - π₂) := by
    have := gibbs_two (x := 1 - π₂) (y := a) (sub_nonneg.2 hπ₂1) (by linarith) ha0 ha1 (fun h => by
        have hor : 0 < π₁ ∨ 0 < π₃ := by
          by_contra hcon
          push Not at hcon
          linarith
        rcases hor with h' | h'
        · exact lt_of_le_of_ne ha0 (ne₁ h').1.symm
        · exact lt_of_le_of_ne ha0 (ne₃ h').2.1.symm) (fun h => by
        have hπ : 0 < π₂ := by linarith
        have := (ne₂ hπ).2.2
        exact sub_pos.1 (lt_of_le_of_ne h1a this.symm))
    rw [show (1 : ℝ) - (1 - π₂) = π₂ by ring] at this
    linarith
  have gb : (1 - π₃) * Real.log b + π₃ * Real.log (1 - b) ≤ - negMulLog π₃ - negMulLog (1 - π₃) := by
    have := gibbs_two (x := 1 - π₃) (y := b) (sub_nonneg.2 hπ₃1) (by linarith) hb0 hb1 (fun h => by
        have hor : 0 < π₁ ∨ 0 < π₂ := by
          by_contra hcon
          push Not at hcon
          linarith
        rcases hor with h' | h'
        · exact lt_of_le_of_ne hb0 (ne₁ h').2.1.symm
        · exact lt_of_le_of_ne hb0 (ne₂ h').1.symm) (fun h => by
        have hπ : 0 < π₃ := by linarith
        have := (ne₃ hπ).2.2
        exact sub_pos.1 (lt_of_le_of_ne h1b this.symm))
    rw [show (1 : ℝ) - (1 - π₃) = π₃ by ring] at this
    linarith
  have gc : (1 - π₁) * Real.log c + π₁ * Real.log (1 - c) ≤ - negMulLog π₁ - negMulLog (1 - π₁) := by
    have := gibbs_two (x := 1 - π₁) (y := c) (sub_nonneg.2 hπ₁1) (by linarith) hc0 hc1 (fun h => by
        have hor : 0 < π₂ ∨ 0 < π₃ := by
          by_contra hcon
          push Not at hcon
          linarith
        rcases hor with h' | h'
        · exact lt_of_le_of_ne hc0 (ne₂ h').2.1.symm
        · exact lt_of_le_of_ne hc0 (ne₃ h').1.symm) (fun h => by
        have hπ : 0 < π₁ := by linarith
        have := (ne₁ hπ).2.2
        exact sub_pos.1 (lt_of_le_of_ne h1c this.symm))
    rw [show (1 : ℝ) - (1 - π₁) = π₁ by ring] at this
    linarith
  -- so `p log S ≤ - ∑ ψ(π_i) ≤ 0`
  have hlogS : Real.log S = (1 / p) * (π₁ * Real.log a + π₁ * Real.log b + π₁ * Real.log (1 - c) +
      (π₂ * Real.log b + π₂ * Real.log c + π₂ * Real.log (1 - a)) +
      (π₃ * Real.log c + π₃ * Real.log a + π₃ * Real.log (1 - b))) +
      (negMulLog π₁ + negMulLog π₂ + negMulLog π₃) := by
    have : Real.log S = (π₁ + π₂ + π₃) * Real.log S := by rw [hπsum, one_mul]
    rw [this, add_mul, add_mul, e₁, e₂, e₃]
    ring
  have hpsi := sum_psi_nonneg hπ₁0 hπ₂0 hπ₃0 hπsum
  have hcoll : π₁ * Real.log a + π₁ * Real.log b + π₁ * Real.log (1 - c) +
      (π₂ * Real.log b + π₂ * Real.log c + π₂ * Real.log (1 - a)) +
      (π₃ * Real.log c + π₃ * Real.log a + π₃ * Real.log (1 - b)) =
      ((1 - π₂) * Real.log a + π₂ * Real.log (1 - a)) + ((1 - π₃) * Real.log b + π₃ * Real.log (1 - b)) +
        ((1 - π₁) * Real.log c + π₁ * Real.log (1 - c)) := by
    have h₁ : π₁ = 1 - π₂ - π₃ := by linarith
    rw [h₁]
    ring
  have hle : Real.log S * p ≤ 0 := by
    have hmul : Real.log S * p = (π₁ * Real.log a + π₁ * Real.log b + π₁ * Real.log (1 - c) +
        (π₂ * Real.log b + π₂ * Real.log c + π₂ * Real.log (1 - a)) +
        (π₃ * Real.log c + π₃ * Real.log a + π₃ * Real.log (1 - b))) +
        p * (negMulLog π₁ + negMulLog π₂ + negMulLog π₃) := by
      rw [hlogS]
      field_simp
    rw [hmul, hcoll, p_eq]
    simp only [psi] at hpsi
    nlinarith
  have hlog0 : Real.log S ≤ 0 := by
    by_contra hcon
    exact absurd hle (not_le.2 (mul_pos (not_le.1 hcon) hp))
  by_contra hcon
  exact absurd hlog0 (not_le.2 (Real.log_pos (not_le.1 hcon)))

/-! ### Three terms -/

/-- The form of (abc) that the induction uses, by homogeneity. -/
theorem rpow_add_rpow_add_rpow_le {f₀ f₁ g₀ g₁ h₀ h₁ : ℝ} (hf₀ : 0 ≤ f₀) (hf₁ : 0 ≤ f₁) (hg₀ : 0 ≤ g₀) (hg₁ : 0 ≤ g₁)
    (hh₀ : 0 ≤ h₀) (hh₁ : 0 ≤ h₁) :
    (f₀ * g₀ * h₀) ^ (1 / p) + (f₁ * g₀ * h₁) ^ (1 / p) + (f₀ * g₁ * h₁) ^ (1 / p) ≤
      ((f₀ + f₁) * (g₀ + g₁) * (h₀ + h₁)) ^ (1 / p) := by
  have hθ : (1 / p) ≠ 0 := (one_div_pos.2 p_pos).ne'
  set F := f₀ + f₁ with hF
  set G := g₀ + g₁ with hG
  set H := h₀ + h₁ with hH
  have hF0 : 0 ≤ F := add_nonneg hf₀ hf₁
  have hG0 : 0 ≤ G := add_nonneg hg₀ hg₁
  have hH0 : 0 ≤ H := add_nonneg hh₀ hh₁
  have hR : 0 ≤ (F * G * H) ^ (1 / p) := Real.rpow_nonneg (mul_nonneg (mul_nonneg hF0 hG0) hH0) _
  have hz : (0 : ℝ) ^ (1 / p) = 0 := Real.zero_rpow hθ
  rcases hF0.eq_or_lt with hFz | hFp
  · have h₀' : f₀ = 0 := by linarith
    have h₁' : f₁ = 0 := by linarith
    simp only [h₀', h₁', zero_mul, hz, add_zero]
    exact hR
  rcases hG0.eq_or_lt with hGz | hGp
  · have h₀' : g₀ = 0 := by linarith
    have h₁' : g₁ = 0 := by linarith
    simp only [h₀', h₁', zero_mul, mul_zero, hz, add_zero]
    exact hR
  rcases hH0.eq_or_lt with hHz | hHp
  · have h₀' : h₀ = 0 := by linarith
    have h₁' : h₁ = 0 := by linarith
    simp only [h₀', h₁', mul_zero, hz, add_zero]
    exact hR
  set a := f₀ / F with ha
  set b := g₀ / G with hb
  set c := h₁ / H with hc
  have hfa : f₀ = F * a := by rw [ha]; field_simp
  have hgb : g₀ = G * b := by rw [hb]; field_simp
  have hhc : h₁ = H * c := by rw [hc]; field_simp
  have hf1a : f₁ = F * (1 - a) := by rw [ha]; field_simp; linarith
  have hg1b : g₁ = G * (1 - b) := by rw [hb]; field_simp; linarith
  have hh1c : h₀ = H * (1 - c) := by rw [hc]; field_simp; linarith
  have ha0 : 0 ≤ a := div_nonneg hf₀ hFp.le
  have ha1 : a ≤ 1 := (div_le_one hFp).2 (by linarith)
  have hb0 : 0 ≤ b := div_nonneg hg₀ hGp.le
  have hb1 : b ≤ 1 := (div_le_one hGp).2 (by linarith)
  have hc0 : 0 ≤ c := div_nonneg hh₁ hHp.le
  have hc1 : c ≤ 1 := (div_le_one hHp).2 (by linarith)
  have hFGH : 0 ≤ F * G * H := (mul_pos (mul_pos hFp hGp) hHp).le
  have e₁ : f₀ * g₀ * h₀ = F * G * H * (a * b * (1 - c)) := by rw [hfa, hgb, hh1c]; ring
  have e₂ : f₁ * g₀ * h₁ = F * G * H * (b * c * (1 - a)) := by rw [hf1a, hgb, hhc]; ring
  have e₃ : f₀ * g₁ * h₁ = F * G * H * (c * a * (1 - b)) := by rw [hfa, hg1b, hhc]; ring
  rw [e₁, e₂, e₃, Real.mul_rpow hFGH (mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.2 hc1)),
    Real.mul_rpow hFGH (mul_nonneg (mul_nonneg hb0 hc0) (sub_nonneg.2 ha1)),
    Real.mul_rpow hFGH (mul_nonneg (mul_nonneg hc0 ha0) (sub_nonneg.2 hb1)), ← mul_add, ← mul_add]
  have := elementary_inequality ha0 ha1 hb0 hb1 hc0 hc1
  exact mul_le_of_le_one_right hR this

/-! ### Counting -/

variable {α : Type*} [DecidableEq α]

/-- The triples `(A₁, A₂, A)` of the three families with `A` the disjoint union of `A₁`, `A₂`. -/
def triples (F G H : Finset (Finset α)) : Finset (Finset α × Finset α × Finset α) :=
  (F ×ˢ G ×ˢ H).filter fun t => Disjoint t.1 t.2.1 ∧ t.1 ∪ t.2.1 = t.2.2

theorem mem_triples {F G H : Finset (Finset α)} {t : Finset α × Finset α × Finset α} :
    t ∈ triples F G H ↔ t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ H ∧ Disjoint t.1 t.2.1 ∧ t.1 ∪ t.2.1 = t.2.2 := by
  simp [triples, and_assoc]

/-- The sets of the family without the element `e`. -/
def famWithout (e : α) (F : Finset (Finset α)) : Finset (Finset α) := F.filter fun x => e ∉ x

/-- The sets of the family with the element `e`, with `e` removed. -/
def famWith (e : α) (F : Finset (Finset α)) : Finset (Finset α) := (F.filter fun x => e ∈ x).image fun x => x.erase e

theorem card_famWithout_add_card_famWith (e : α) (F : Finset (Finset α)) :
    (famWithout e F).card + (famWith e F).card = F.card := by
  have hinj : Set.InjOn (fun x : Finset α => x.erase e) (F.filter fun x => e ∈ x : Finset (Finset α)) := by
    intro x hx y hy h
    have hxe := (mem_filter.1 (mem_coe.1 hx)).2
    have hye := (mem_filter.1 (mem_coe.1 hy)).2
    rw [← insert_erase hxe, ← insert_erase hye]
    exact congrArg (insert e) h
  rw [famWith, card_image_of_injOn hinj, famWithout, add_comm]
  exact card_filter_add_card_filter_not _

theorem subset_of_mem_famWithout {e : α} {F : Finset (Finset α)} {U : Finset α} (hF : ∀ x ∈ F, x ⊆ insert e U) {x : Finset α}
    (hx : x ∈ famWithout e F) : x ⊆ U := by
  obtain ⟨hxF, hxe⟩ := mem_filter.1 hx
  intro y hy
  rcases mem_insert.1 (hF x hxF hy) with h | h
  · exact absurd (h ▸ hy) hxe
  · exact h

theorem subset_of_mem_famWith {e : α} {F : Finset (Finset α)} {U : Finset α} (hF : ∀ x ∈ F, x ⊆ insert e U) {x : Finset α}
    (hx : x ∈ famWith e F) : x ⊆ U := by
  obtain ⟨x', hx', rfl⟩ := mem_image.1 hx
  obtain ⟨hxF, -⟩ := mem_filter.1 hx'
  intro y hy
  obtain ⟨hye, hyx⟩ := mem_erase.1 hy
  exact (mem_insert.1 (hF x' hxF hyx)).resolve_left hye

/-- **One coordinate of the induction**: a triple has the element `e` in none of its sets, or in `A₁` and `A`, or in `A₂` and `A`. -/
theorem card_triples_le_add (e : α) (F G H : Finset (Finset α)) :
    (triples F G H).card ≤ (triples (famWithout e F) (famWithout e G) (famWithout e H)).card +
      (triples (famWith e F) (famWithout e G) (famWith e H)).card +
      (triples (famWithout e F) (famWith e G) (famWith e H)).card := by
  set S := triples F G H with hS
  have hunion : S ⊆ (S.filter fun t => e ∉ t.1 ∧ e ∉ t.2.1) ∪ (S.filter fun t => e ∈ t.1) ∪ (S.filter fun t => e ∈ t.2.1) := by
    intro t ht
    simp only [mem_union, mem_filter]
    by_cases h₁ : e ∈ t.1
    · exact Or.inl (Or.inr ⟨ht, h₁⟩)
    · by_cases h₂ : e ∈ t.2.1
      · exact Or.inr ⟨ht, h₂⟩
      · exact Or.inl (Or.inl ⟨ht, h₁, h₂⟩)
  have h₀ : (S.filter fun t => e ∉ t.1 ∧ e ∉ t.2.1).card ≤
      (triples (famWithout e F) (famWithout e G) (famWithout e H)).card := by
    refine card_le_card fun t ht => ?_
    obtain ⟨ht', h₁, h₂⟩ := mem_filter.1 ht
    obtain ⟨hF, hG, hH, hd, hu⟩ := mem_triples.1 ht'
    refine mem_triples.2 ⟨mem_filter.2 ⟨hF, h₁⟩, mem_filter.2 ⟨hG, h₂⟩, mem_filter.2 ⟨hH, ?_⟩, hd, hu⟩
    rw [← hu]
    simp [h₁, h₂]
  have hinj : ∀ {x x' : Finset α}, e ∈ x → e ∈ x' → x.erase e = x'.erase e → x = x' := fun hx hx' h => by
    rw [← insert_erase hx, ← insert_erase hx', h]
  have h₁ : (S.filter fun t => e ∈ t.1).card ≤ (triples (famWith e F) (famWithout e G) (famWith e H)).card := by
    refine card_le_card_of_injOn (fun t => (t.1.erase e, t.2.1, t.2.2.erase e)) (fun t ht => ?_) ?_
    · obtain ⟨ht', he⟩ := mem_filter.1 (mem_coe.1 ht)
      obtain ⟨hF, hG, hH, hd, hu⟩ := mem_triples.1 ht'
      have he₂ : e ∉ t.2.1 := disjoint_left.1 hd he
      have he₃ : e ∈ t.2.2 := hu ▸ mem_union_left _ he
      refine mem_coe.2 (mem_triples.2 ⟨mem_image.2 ⟨t.1, mem_filter.2 ⟨hF, he⟩, rfl⟩, mem_filter.2 ⟨hG, he₂⟩,
        mem_image.2 ⟨t.2.2, mem_filter.2 ⟨hH, he₃⟩, rfl⟩, ?_, ?_⟩)
      · exact disjoint_of_subset_left (erase_subset _ _) hd
      · simp only
        rw [← hu, erase_union_distrib, erase_eq_of_notMem he₂]
    · rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' h
      obtain ⟨hA, he⟩ := mem_filter.1 (mem_coe.1 ht)
      obtain ⟨hA', he'⟩ := mem_filter.1 (mem_coe.1 ht')
      obtain ⟨-, -, -, -, hu⟩ := mem_triples.1 hA
      obtain ⟨-, -, -, -, hu'⟩ := mem_triples.1 hA'
      simp only [Prod.mk.injEq] at h he he' hu hu' ⊢
      obtain ⟨h₁, h₂, h₃⟩ := h
      have hz : e ∈ z := hu ▸ mem_union_left _ he
      have hz' : e ∈ z' := hu' ▸ mem_union_left _ he'
      exact ⟨hinj he he' h₁, h₂, hinj hz hz' h₃⟩
  have h₂ : (S.filter fun t => e ∈ t.2.1).card ≤ (triples (famWithout e F) (famWith e G) (famWith e H)).card := by
    refine card_le_card_of_injOn (fun t => (t.1, t.2.1.erase e, t.2.2.erase e)) (fun t ht => ?_) ?_
    · obtain ⟨ht', he⟩ := mem_filter.1 (mem_coe.1 ht)
      obtain ⟨hF, hG, hH, hd, hu⟩ := mem_triples.1 ht'
      have he₁ : e ∉ t.1 := fun h => disjoint_left.1 hd h he
      have he₃ : e ∈ t.2.2 := hu ▸ mem_union_right _ he
      refine mem_coe.2 (mem_triples.2 ⟨mem_filter.2 ⟨hF, he₁⟩, mem_image.2 ⟨t.2.1, mem_filter.2 ⟨hG, he⟩, rfl⟩,
        mem_image.2 ⟨t.2.2, mem_filter.2 ⟨hH, he₃⟩, rfl⟩, ?_, ?_⟩)
      · exact disjoint_of_subset_right (erase_subset _ _) hd
      · simp only
        rw [← hu, erase_union_distrib, erase_eq_of_notMem he₁]
    · rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' h
      obtain ⟨hA, he⟩ := mem_filter.1 (mem_coe.1 ht)
      obtain ⟨hA', he'⟩ := mem_filter.1 (mem_coe.1 ht')
      obtain ⟨-, -, -, -, hu⟩ := mem_triples.1 hA
      obtain ⟨-, -, -, -, hu'⟩ := mem_triples.1 hA'
      simp only [Prod.mk.injEq] at h he he' hu hu' ⊢
      obtain ⟨h₁, h₂, h₃⟩ := h
      have hz : e ∈ z := hu ▸ mem_union_right _ he
      have hz' : e ∈ z' := hu' ▸ mem_union_right _ he'
      exact ⟨h₁, hinj he he' h₂, hinj hz hz' h₃⟩
  calc S.card ≤ _ := card_le_card hunion
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add h₀ h₁) h₂

/-- **The bound on three families**, the source's second remark (`ext:kane_tao_main`): at most `(|F| |G| |H|)^(1/p)` triples of the three families have the third
set the disjoint union of the first two. By induction on the elements of a ground set: `card_triples_le_add` splits the triples by the place of an element, the three parts are
bounded by induction, and `rpow_add_rpow_add_rpow_le` adds the bounds. The source tensorizes a convolution inequality for functions instead, in blocks of
coordinates; it applies that to indicator functions. -/
theorem card_triples_le_of_subset (U : Finset α) :
    ∀ F G H : Finset (Finset α), (∀ x ∈ F, x ⊆ U) → (∀ x ∈ G, x ⊆ U) → (∀ x ∈ H, x ⊆ U) →
      ((triples F G H).card : ℝ) ≤ ((F.card : ℝ) * G.card * H.card) ^ (1 / p) := by
  have hθ : (1 / p) ≠ 0 := (one_div_pos.2 p_pos).ne'
  induction U using Finset.induction_on with
  | empty =>
    intro F G H hF hG hH
    have hsub : ∀ {F : Finset (Finset α)}, (∀ x ∈ F, x ⊆ ∅) → F.card ≤ 1 := fun {F} hF => by
      refine card_le_one.2 fun x hx y hy => ?_
      rw [subset_empty.1 (hF x hx), subset_empty.1 (hF y hy)]
    have hle : (triples F G H).card ≤ F.card * G.card * H.card := by
      refine (card_le_card (filter_subset _ _)).trans ?_
      rw [card_product, card_product, mul_assoc]
    have h₁ := hsub hF
    have h₂ := hsub hG
    have h₃ := hsub hH
    have hmul : F.card * G.card * H.card ≤ 1 := by
      calc F.card * G.card * H.card ≤ 1 * 1 * 1 := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
        _ = 1 := rfl
    have hcases : F.card * G.card * H.card = 0 ∨ F.card * G.card * H.card = 1 := by omega
    have hcast : ((F.card : ℝ) * G.card * H.card) = ((F.card * G.card * H.card : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    rcases hcases with h | h
    · rw [h] at hle ⊢
      have h0 : (triples F G H).card = 0 := by omega
      rw [h0, Nat.cast_zero]
      exact Real.rpow_nonneg (le_refl _) _
    · rw [h] at hle ⊢
      simpa using (by exact_mod_cast hle : ((triples F G H).card : ℝ) ≤ 1)
  | insert e U heU ih =>
    intro F G H hF hG hH
    have hstep : ((triples F G H).card : ℝ) ≤ ((triples (famWithout e F) (famWithout e G) (famWithout e H)).card : ℝ) +
        ((triples (famWith e F) (famWithout e G) (famWith e H)).card : ℝ) +
        ((triples (famWithout e F) (famWith e G) (famWith e H)).card : ℝ) := by
      exact_mod_cast card_triples_le_add e F G H
    have i₀ := ih (famWithout e F) (famWithout e G) (famWithout e H) (fun _ hx => subset_of_mem_famWithout hF hx)
      (fun _ hx => subset_of_mem_famWithout hG hx) (fun _ hx => subset_of_mem_famWithout hH hx)
    have i₁ := ih (famWith e F) (famWithout e G) (famWith e H) (fun _ hx => subset_of_mem_famWith hF hx)
      (fun _ hx => subset_of_mem_famWithout hG hx) (fun _ hx => subset_of_mem_famWith hH hx)
    have i₂ := ih (famWithout e F) (famWith e G) (famWith e H) (fun _ hx => subset_of_mem_famWithout hF hx)
      (fun _ hx => subset_of_mem_famWith hG hx) (fun _ hx => subset_of_mem_famWith hH hx)
    have hthree := rpow_add_rpow_add_rpow_le (f₀ := (famWithout e F).card) (f₁ := (famWith e F).card)
      (g₀ := (famWithout e G).card) (g₁ := (famWith e G).card) (h₀ := (famWithout e H).card) (h₁ := (famWith e H).card)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hc : ∀ F : Finset (Finset α), ((famWithout e F).card : ℝ) + (famWith e F).card = F.card := fun F => by
      exact_mod_cast card_famWithout_add_card_famWith e F
    rw [hc, hc, hc] at hthree
    linarith

/-- **The bound on three families**, with the ground set left implicit. -/
theorem card_triples_le (F G H : Finset (Finset α)) :
    ((triples F G H).card : ℝ) ≤ ((F.card : ℝ) * G.card * H.card) ^ (1 / p) :=
  card_triples_le_of_subset ((F ∪ G ∪ H).sup id) F G H
    (fun _ hx => le_sup (f := id) (mem_union_left _ (mem_union_left _ hx)))
    (fun _ hx => le_sup (f := id) (mem_union_left _ (mem_union_right _ hx)))
    (fun _ hx => le_sup (f := id) (mem_union_right _ hx))

/-- **Theorem 1 of the source** (`ext:kane_tao_main`), the bound: `|{(A₁, A₂, A) ∈ X³ : A = A₁ ⊎ A₂}| ≤ |X|^(3/p)` for a finite collection `X` of finite sets, with
`p = log₃(27/4)`. That `p` cannot be larger is not formalized. -/
theorem theorem1 (X : Finset (Finset α)) : ((triples X X X).card : ℝ) ≤ (X.card : ℝ) ^ (3 / p) := by
  have h := card_triples_le X X X
  have hX : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have heq : ((X.card : ℝ) * X.card * X.card) ^ (1 / p) = (X.card : ℝ) ^ (3 / p) := by
    rw [show (X.card : ℝ) * X.card * X.card = (X.card : ℝ) ^ (3 : ℝ) by
      rw [Real.rpow_ofNat]; ring, ← Real.rpow_mul hX]
    congr 1
    ring
  rwa [heq] at h

/-- **The form ASTRAL-III prints**: `|Y| = O(|X|^1.726)`, here with constant one. -/
theorem card_triples_le_rpow (X : Finset (Finset α)) : ((triples X X X).card : ℝ) ≤ (X.card : ℝ) ^ (1.726 : ℝ) := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp [triples]
    positivity
  · refine (theorem1 X).trans (Real.rpow_le_rpow_of_exponent_le ?_ three_div_p_le)
    exact_mod_cast card_pos.2 hne

end External.KaneTao2017
