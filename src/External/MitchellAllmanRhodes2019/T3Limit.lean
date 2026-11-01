module

public import External.MitchellAllmanRhodes2019.T3Density

/-!
# The limit law of the T3 statistic

Mitchell, Allman, Rhodes 2019, Proposition 4.1, for the trinomial: the likelihood ratio statistic of model T3, at a point
`(1 - 2φ/3, φ/3, φ/3)`, `0 < φ ≤ 1`, of its null, and the variable `t3Var φ` of that proposition under `N((0, μ₀(n)), I)`
converge in distribution to the same limit (`External.MitchellAllmanRhodes2019.proposition4_1`).

At the singularity `φ = 1` the source says more: "Although this distribution is not a `χ²`, it is exactly the asymptotic
distribution". This is `QuartetTests.t3Stat_limitLaw`, and in the other forms `QuartetTests.tendstoInDistribution_t3Stat`,
`QuartetTests.t3Stat_limitLaw_density`, the last with the density of Proposition 4.2, which at the singularity is
`3 / (2 √(2 π λ)) exp (-λ / 2) (1 - erf √(λ / 6))` (`QuartetTests.t3Density_one`). That it is not a `χ²` is
`QuartetTests.map_t3Var_one_ne_chiSqLaw`.

The statistic is the likelihood ratio statistic of the source: `Trinomial.t3S_eq_likelihoodRatio`, for positive counts.

The argument is the source's, with one step replaced. In the whitened coordinates of its Appendix B the three T1 statistics
are the squared distances to the three half-lines, up to an error that vanishes on bounded sets (`Trinomial.closeOnBalls_t3S_centroid`):
the first argument of Equation `eq:T3dis` for the vertical half-line, and the second for the other two; the least of them
is the variable (`QuartetTests.t3Var_eq_halfLineDist`).

Departure from the source: the source gets the limit of the likelihood ratio from its Theorem 3.1, and so from van der Vaart,
*Asymptotic Statistics*, Theorem 16.7, which rests on differentiability in quadratic mean, local asymptotic normality and the
consistency of maximum likelihood estimates. Mathlib has none of these. Here this step is the special case for this model, from
the central limit theorem (`Trinomial.tendstoInDistribution_sampleW`) and the extended continuous mapping theorem, as in
`External.MitchellAllmanRhodes2019.cutModel_theorem31`, and the replacement of the model's segments by half-lines is part of the
proof, not a further step.

With the true parameter, the p-value at the singularity is asymptotically uniform (`QuartetTests.t3Tail_t3Stat_asymptoticallyUniform`).
The tightness of the statistic that `QuartetTests.t3Test_nonCollapse` uses is not replaced: that theorem holds at every point of
the null and needs no limit law.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Classical
open External.MitchellAllmanRhodes2019 (normalSample normalSample_map_sub)

namespace Phylogenetics.Trinomial

open Phylogenetics.QuartetTests

/-- The likelihood ratio statistic of model T3, on real counts: the least of the three T1 statistics. -/
def t3S (a b c : ℝ) : ℝ :=
  min (if (b + c) / 2 ≤ a then lineS b c else starS a b c)
    (min (if (a + c) / 2 ≤ b then lineS a c else starS a b c)
      (if (a + b) / 2 ≤ c then lineS a b else starS a b c))

/-! ### The statistic is the likelihood ratio statistic -/

/-- The log-likelihood of the counts `a`, `b`, `c` at `p`, up to the multinomial coefficient, which the ratio cancels. -/
def logLik (a b c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  a * Real.log p.1 + b * Real.log p.2.1 + c * Real.log p.2.2

/-- The open simplex, the source's `Δ²`. -/
def openSimplex : Set (ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1}

/-- The null of model T3, the source's `Θ₀`, where `q = φ₀ / 3`, `φ₀ ∈ (0, 1]`. -/
def t3Null : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 3 ∧
    (p = (1 - 2 * q, q, q) ∨ p = (q, 1 - 2 * q, q) ∨ p = (q, q, 1 - 2 * q))}

/-- The log-likelihood at the frequencies, for counts summing to `N`. -/
def logLikHat (N a b c : ℝ) : ℝ :=
  a * Real.log (a / N) + b * Real.log (b / N) + c * Real.log (c / N)

lemma mul_log_le {x p y : ℝ} (hx : 0 ≤ x) (hp : 0 < p) (hy : 0 < y) :
    x * Real.log p ≤ x * Real.log y + x * (p / y - 1) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hp hy)
  rw [Real.log_div hp.ne' hy.ne'] at h
  have := mul_le_mul_of_nonneg_left h hx
  linarith

/-- The frequencies maximize the log-likelihood on the open simplex. -/
lemma isGreatest_logLik {a b c N : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hN : a + b + c = N) : IsGreatest (logLik a b c '' openSimplex) (logLikHat N a b c) := by
  have hNpos : 0 < N := by rw [← hN]; positivity
  constructor
  · refine ⟨(a / N, b / N, c / N), ⟨by simp only; positivity, by simp only; positivity,
      by simp only; positivity, ?_⟩, rfl⟩
    simp only
    rw [← hN]
    field_simp
  · rintro _ ⟨⟨p₀, p₁, p₂⟩, ⟨h₀, h₁, h₂, hp⟩, rfl⟩
    simp only at h₀ h₁ h₂ hp
    have l₀ := mul_log_le ha.le h₀ (div_pos ha hNpos)
    have l₁ := mul_log_le hb.le h₁ (div_pos hb hNpos)
    have l₂ := mul_log_le hc.le h₂ (div_pos hc hNpos)
    have e₀ : a * (p₀ / (a / N) - 1) = N * p₀ - a := by field_simp
    have e₁ : b * (p₁ / (b / N) - 1) = N * p₁ - b := by field_simp
    have e₂ : c * (p₂ / (c / N) - 1) = N * p₂ - c := by field_simp
    rw [e₀] at l₀
    rw [e₁] at l₁
    rw [e₂] at l₂
    have hsum : N * p₀ + N * p₁ + N * p₂ = a + b + c := by
      rw [hN]
      linear_combination N * hp
    simp only [logLik, logLikHat]
    linarith

/-- The best point of the half-line of the first topology: on the line when `a` is at least the mean of `b`, `c`, and
otherwise the centroid. This is what `t1Stat` says of the T1 null. -/
lemma halfLine_max {a b c N : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hN : a + b + c = N) :
    ∃ q₀ : ℝ, 0 < q₀ ∧ q₀ ≤ 1 / 3 ∧
      logLik a b c (1 - 2 * q₀, q₀, q₀) =
        logLikHat N a b c - (if (b + c) / 2 ≤ a then lineS b c else starS a b c) / 2 ∧
      ∀ q : ℝ, 0 < q → q ≤ 1 / 3 → logLik a b c (1 - 2 * q, q, q) ≤
        logLikHat N a b c - (if (b + c) / 2 ≤ a then lineS b c else starS a b c) / 2 := by
  have hNpos : 0 < N := by rw [← hN]; positivity
  have hbc : 0 < b + c := by positivity
  simp only [logLik]
  split_ifs with hle
  · set q₀ := (b + c) / (2 * N) with hq₀
    have hq₀pos : 0 < q₀ := by positivity
    have h1 : 1 - 2 * q₀ = a / N := by
      rw [hq₀, ← hN]
      field_simp
      ring
    have hval : a * Real.log (a / N) + b * Real.log q₀ + c * Real.log q₀ =
        logLikHat N a b c - lineS b c / 2 := by
      have hlog : Real.log q₀ = Real.log (b + c) - (Real.log 2 + Real.log N) := by
        rw [hq₀, Real.log_div hbc.ne' (by positivity), Real.log_mul (by norm_num) hNpos.ne']
      unfold logLikHat lineS
      rw [hlog, Real.log_div hb.ne' hNpos.ne', Real.log_div hc.ne' hNpos.ne']
      ring
    refine ⟨q₀, hq₀pos, ?_, ?_, fun q hq hq3 => ?_⟩
    · rw [hq₀, div_le_iff₀ (by positivity), ← hN]
      linarith
    · simp only [h1]
      exact hval
    · rw [← hval]
      have l₀ := mul_log_le ha.le (by linarith : 0 < 1 - 2 * q) (div_pos ha hNpos)
      have l₁ := mul_log_le hbc.le hq hq₀pos
      have e₀ : a * ((1 - 2 * q) / (a / N) - 1) = N * (1 - 2 * q) - a := by field_simp
      have e₁ : (b + c) * (q / q₀ - 1) = 2 * N * q - (b + c) := by
        rw [hq₀]
        field_simp
      rw [e₀] at l₀
      rw [e₁] at l₁
      have hsum : N = a + b + c := hN.symm
      nlinarith
  · have hlt : a < (b + c) / 2 := not_le.1 hle
    have h3 : (0 : ℝ) < 1 / 3 := by norm_num
    have hval : a * Real.log (1 / 3) + b * Real.log (1 / 3) + c * Real.log (1 / 3) =
        logLikHat N a b c - starS a b c / 2 := by
      have hlog3 : Real.log (1 / 3) = -Real.log 3 := by
        rw [one_div, Real.log_inv]
      unfold logLikHat starS
      rw [hN, hlog3, Real.log_div ha.ne' hNpos.ne', Real.log_div hb.ne' hNpos.ne',
        Real.log_div hc.ne' hNpos.ne', Real.log_div hNpos.ne' (by norm_num)]
      rw [← hN]
      ring
    refine ⟨1 / 3, h3, le_rfl, ?_, fun q hq hq3 => ?_⟩
    · rw [show (1 : ℝ) - 2 * (1 / 3) = 1 / 3 by norm_num]
      exact hval
    · rw [← hval]
      have l₀ := mul_log_le ha.le (by linarith : 0 < 1 - 2 * q) h3
      have l₁ := mul_log_le hbc.le hq h3
      have e₀ : a * ((1 - 2 * q) / (1 / 3) - 1) = a * (2 - 6 * q) := by
        field_simp
        ring
      have e₁ : (b + c) * (q / (1 / 3) - 1) = (b + c) * (3 * q - 1) := by
        field_simp
      rw [e₀] at l₀
      rw [e₁] at l₁
      have hneg : (3 * q - 1) * (b + c - 2 * a) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      nlinarith

lemma starS_swap (a b c : ℝ) : starS b a c = starS a b c := by
  unfold starS
  rw [add_comm b a]
  ring

lemma starS_rot (a b c : ℝ) : starS c a b = starS a b c := by
  unfold starS
  rw [show c + a + b = a + b + c by ring]
  ring

lemma logLikHat_swap (N a b c : ℝ) : logLikHat N b a c = logLikHat N a b c := by
  unfold logLikHat
  ring

lemma logLikHat_rot (N a b c : ℝ) : logLikHat N c a b = logLikHat N a b c := by
  unfold logLikHat
  ring

/-- **The T3 statistic is the likelihood ratio statistic of the source** (`ext:t3_lrt`) (Section 3 of Mitchell, Allman, Rhodes 2019, `Λ_n`) for
testing `Θ₀` against the open simplex, on positive counts. On a boundary count the suprema are not attained, and the statistic is
their continuous extension; such counts have vanishing probability at a point of the open simplex. -/
theorem t3S_eq_likelihoodRatio {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    t3S a b c = 2 * (sSup (logLik a b c '' openSimplex) - sSup (logLik a b c '' t3Null)) := by
  have hN : a + b + c = a + b + c := rfl
  obtain ⟨q₁, hq₁, hq₁', hv₁, hu₁⟩ := halfLine_max ha hb hc hN
  obtain ⟨q₂, hq₂, hq₂', hv₂, hu₂⟩ := halfLine_max hb ha hc (by ring : b + a + c = a + b + c)
  obtain ⟨q₃, hq₃, hq₃', hv₃, hu₃⟩ := halfLine_max hc ha hb (by ring : c + a + b = a + b + c)
  rw [starS_swap, logLikHat_swap] at hv₂ hu₂
  rw [starS_rot, logLikHat_rot] at hv₃ hu₃
  have hswap : ∀ q : ℝ, logLik b a c (1 - 2 * q, q, q) = logLik a b c (q, 1 - 2 * q, q) := by
    intro q
    simp only [logLik]
    ring
  have hrot : ∀ q : ℝ, logLik c a b (1 - 2 * q, q, q) = logLik a b c (q, q, 1 - 2 * q) := by
    intro q
    simp only [logLik]
    ring
  simp only [hswap] at hv₂ hu₂
  simp only [hrot] at hv₃ hu₃
  have hL := (isGreatest_logLik ha hb hc hN).csSup_eq
  set L := logLikHat (a + b + c) a b c
  have hle₁ : t3S a b c ≤ if (b + c) / 2 ≤ a then lineS b c else starS a b c := min_le_left _ _
  have hle₂ : t3S a b c ≤ if (a + c) / 2 ≤ b then lineS a c else starS a b c :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hle₃ : t3S a b c ≤ if (a + b) / 2 ≤ c then lineS a b else starS a b c :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hG : IsGreatest (logLik a b c '' t3Null) (L - t3S a b c / 2) := by
    constructor
    · have hmem : ∀ {q : ℝ} {p : ℝ × ℝ × ℝ}, 0 < q → q ≤ 1 / 3 →
          (p = (1 - 2 * q, q, q) ∨ p = (q, 1 - 2 * q, q) ∨ p = (q, q, 1 - 2 * q)) → p ∈ t3Null :=
        fun h h' h'' => ⟨_, h, h', h''⟩
      rcases min_choice (if (b + c) / 2 ≤ a then lineS b c else starS a b c)
          (min (if (a + c) / 2 ≤ b then lineS a c else starS a b c)
            (if (a + b) / 2 ≤ c then lineS a b else starS a b c)) with h | h
      · refine ⟨_, hmem hq₁ hq₁' (Or.inl rfl), ?_⟩
        rw [hv₁, t3S, h]
      · rcases min_choice (if (a + c) / 2 ≤ b then lineS a c else starS a b c)
            (if (a + b) / 2 ≤ c then lineS a b else starS a b c) with h' | h'
        · refine ⟨_, hmem hq₂ hq₂' (Or.inr (Or.inl rfl)), ?_⟩
          rw [hv₂, t3S, h, h']
        · refine ⟨_, hmem hq₃ hq₃' (Or.inr (Or.inr rfl)), ?_⟩
          rw [hv₃, t3S, h, h']
    · rintro _ ⟨p, ⟨q, hq, hq3, hp⟩, rfl⟩
      rcases hp with rfl | rfl | rfl
      · have := hu₁ q hq hq3
        linarith
      · have := hu₂ q hq hq3
        linarith
      · have := hu₃ q hq hq3
        linarith
  rw [hL, hG.csSup_eq]
  ring

/-- The singularity is a point of the cut model. -/
theorem one_mem_cutRange : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num

lemma scaleA_one_eq : scaleA 1 = √3 * scaleB 1 := by
  have hA := scaleA_pos one_mem_cutRange
  have hB := scaleB_pos one_mem_cutRange
  have hA2 := scaleA_sq one_mem_cutRange
  have hB2 := scaleB_sq one_mem_cutRange
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine (sq_eq_sq₀ hA.le (by positivity)).1 ?_
  rw [mul_pow, hA2, hB2, h3]
  norm_num

/-- At the centroid, each count is at least the mean of the other two exactly on the side of its half-line. -/
lemma centroid_sides {n : ℕ} (hn : 0 < n) {a b c : ℝ} (hsum : a + b + c = n) :
    a - (b + c) / 2 = 3 / 2 * (√(n : ℝ) * scaleB 1) *
        ((whiten 1 n a b c).1 * 0 + (whiten 1 n a b c).2 * 1) ∧
      b - (a + c) / 2 = 3 / 2 * (√(n : ℝ) * scaleB 1) *
        ((whiten 1 n a b c).1 * (√3 / 2) + (whiten 1 n a b c).2 * -(1 / 2)) ∧
      c - (a + b) / 2 = 3 / 2 * (√(n : ℝ) * scaleB 1) *
        ((whiten 1 n a b c).1 * -(√3 / 2) + (whiten 1 n a b c).2 * -(1 / 2)) := by
  obtain ⟨ha, hb, hc⟩ := whiten_counts one_mem_cutRange hn hsum
  rw [scaleA_one_eq] at hb hc
  generalize (whiten 1 n a b c).1 = x at *
  generalize (whiten 1 n a b c).2 = y at *
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ha - hb / 2 - hc / 2
  · linear_combination hb - ha / 2 - hc / 2
  · linear_combination hc - ha / 2 - hb / 2

lemma le_iff_of_sub_eq {a m K w : ℝ} (hK : 0 < K) (h : a - m = K * w) : m ≤ a ↔ 0 ≤ w := by
  rw [← sub_nonneg, h]
  exact mul_nonneg_iff_of_pos_left hK

lemma abs_ite_sub_lt {P Q : Prop} [Decidable P] [Decidable Q] {L S p d ε : ℝ} (hPQ : P ↔ Q)
    (hL : |L - p| < ε) (hS : |S - d| < ε) :
    |(if P then L else S) - (if Q then p else d)| < ε := by
  by_cases hQ : Q
  · rw [ite_eq_left hQ, ite_eq_left (hPQ.2 hQ)]
    exact hL
  · rw [ite_eq_right hQ, ite_eq_right fun hP => hQ (hPQ.1 hP)]
    exact hS

/-- At the singularity, the T1 statistic of each topology is close to the squared distance to its half-line, uniformly on
bounded sets of the whitened frequencies, and so the T3 statistic is close to the least of the three: the source's
minimum squared distance from the sample point to the transformed null. -/
theorem closeOnBalls_t3S_centroid :
    CloseOnBalls (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW 1 η)
      (fun (n : ℕ) (η : Fin n → Fin 3) ↦ t3S (count η 0) (count η 1) (count η 2))
      (halfLineDist (1 / 2) (√3 / 2)) := by
  intro R hR ε hε
  filter_upwards [eventually_lineS_first one_mem_cutRange hR hε, eventually_lineS_second_centroid hR hε,
    eventually_lineS_third_centroid hR hε, eventually_starS_centroid hR hε, eventually_gt_atTop 0]
    with n h₁ h₂ h₃ h₄ hn0 η hη₁ hη₂
  have hsum := count_add η
  have hη₁' : |(whiten 1 n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
  have hη₂' : |(whiten 1 n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
  have hl₁ := h₁ _ _ _ hsum hη₁' hη₂'
  have hl₂ := h₂ _ _ _ hsum hη₁' hη₂'
  have hl₃ := h₃ _ _ _ hsum hη₁' hη₂'
  have hst := h₄ _ _ _ hsum hη₁' hη₂'
  obtain ⟨e₁, e₂, e₃⟩ := centroid_sides hn0 hsum
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  have hK : 0 < 3 / 2 * (√(n : ℝ) * scaleB 1) := by
    have := scaleB_pos one_mem_cutRange
    positivity
  change |t3S _ _ _ - halfLineDist (1 / 2) (√3 / 2) (whiten 1 n _ _ _)| < ε
  simp only [t3S, halfLineDist, sqDistHalfLine]
  refine abs_min_sub_min_lt (abs_ite_sub_lt (le_iff_of_sub_eq hK e₁) ?_ hst)
    (abs_min_sub_min_lt (abs_ite_sub_lt (le_iff_of_sub_eq hK e₂) ?_ hst)
      (abs_ite_sub_lt (le_iff_of_sub_eq hK e₃) ?_ hst))
  · rwa [show ∀ x y : ℝ, (x * 1 - y * 0) ^ 2 = x ^ 2 from fun x y => by ring]
  · rwa [show ∀ x y : ℝ, (x * -(1 / 2) - y * (√3 / 2)) ^ 2 = (1 / 2 * x + √3 / 2 * y) ^ 2 from
      fun x y => by ring]
  · rwa [show ∀ x y : ℝ, (x * -(1 / 2) - y * -(√3 / 2)) ^ 2 = (1 / 2 * x - √3 / 2 * y) ^ 2 from
      fun x y => by ring]

theorem sq_add_sq_centroid : ((1 : ℝ) / 2) ^ 2 + (√3 / 2) ^ 2 = 1 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [div_pow, div_pow, h3]
  norm_num

/-- At the singularity, the variable of Proposition 4.1 is the distance to the three half-lines at the angles of the
centroid, almost surely. -/
theorem t3Var_one_ae_eq : t3Var 1 =ᵐ[stdPlane] halfLineDist (1 / 2) (√3 / 2) := by
  have h := t3Var_ae_eq_halfLineDist (φ := 1) (by norm_num) 0
  rwa [alphaZero_one, Real.sin_pi_div_six, Real.cos_pi_div_six] at h

/-- **The limit law at the singularity, for the trinomial.** -/
theorem tendstoInDistribution_t3S_centroid :
    TendstoInDistribution (fun (n : ℕ) (η : Fin n → Fin 3) ↦ t3S (count η 0) (count η 1) (count η 2))
      atTop (t3Var 1) (fun n ↦ Measure.pi fun _ : Fin n ↦ (cutPoint_isDist one_mem_cutRange).toPMF.toMeasure)
      stdPlane := by
  have h := tendstoInDistribution_of_closeOnBalls (tendstoInDistribution_sampleW one_mem_cutRange)
    (S := fun (n : ℕ) (η : Fin n → Fin 3) ↦ t3S (count η 0) (count η 1) (count η 2))
    (fun n ↦ Measurable.of_discrete.aemeasurable) (continuous_halfLineDist sq_add_sq_centroid)
    closeOnBalls_t3S_centroid
  exact h.congr (fun _ ↦ Filter.EventuallyEq.rfl) t3Var_one_ae_eq.symm

/-- The tail of the limit: `μ₀ = 0` for every sample size at the singularity, so that `t3Tail 1 m` does not depend on `m`. -/
theorem t3Tail_one_eq (m t : ℝ) :
    t3Tail 1 m t = stdPlane.real {z | t < halfLineDist (1 / 2) (√3 / 2) z} := by
  have hset : ({z | t < t3Var 1 z} : Set (ℝ × ℝ)) =ᵐ[stdPlane]
      {z | t < halfLineDist (1 / 2) (√3 / 2) z} := by
    filter_upwards [t3Var_one_ae_eq] with z hz
    apply propext
    rw [hz]
  rw [t3Tail, muZero_one, measureReal_def, measureReal_def]
  exact congrArg ENNReal.toReal (measure_congr hset)

/-- The limit has no atoms. -/
theorem stdPlane_halfLineDist_eq_null (t : ℝ) :
    stdPlane {z | halfLineDist (1 / 2) (√3 / 2) z = t} = 0 := by
  have h := measure_halfLineDist_eq_null (φ := 1) (by norm_num) 0 t
  rwa [alphaZero_one, Real.sin_pi_div_six, Real.cos_pi_div_six, muZero_one] at h

/-- **The distribution function of the T3 statistic at the singularity**, for the trinomial: its tail at every `t` tends to that
of the limit law. -/
theorem tendsto_iidProb_lt_t3S_centroid (m t : ℝ) :
    Tendsto (fun n ↦ iidProb (cutPoint 1) n fun η ↦ t < t3S (count η 0) (count η 1) (count η 2)) atTop
      (𝓝 (t3Tail 1 m t)) := by
  rw [t3Tail_one_eq]
  refine tendsto_iidProb_of_threshold one_mem_cutRange (continuous_halfLineDist sq_add_sq_centroid)
    ?_ ?_ (stdPlane_halfLineDist_eq_null t)
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t3S_centroid R hR δ hδ] with n hn η h₁ h₂ h₃
    have := (abs_lt.1 (hn η h₁ h₂)).1
    linarith
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t3S_centroid R hR δ hδ] with n hn η h₁ h₂ h₃ h₄
    have := (abs_lt.1 (hn η h₁ h₂)).2
    linarith

/-! ### Off the singularity -/

/-- Off the singularity, the T3 statistic is the statistic of the true line, and so close to `Z²`: "the minimum in the formula
tends toward selecting the first argument". -/
theorem closeOnBalls_t3S_of_lt {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) :
    CloseOnBalls (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW φ η)
      (fun (n : ℕ) (η : Fin n → Fin 3) ↦ t3S (count η 0) (count η 1) (count η 2))
      (fun z ↦ z.1 ^ 2) := by
  intro R hR ε hε
  filter_upwards [eventually_lineS_first hφ hR (lt_min hε one_pos),
    eventually_lineS_other_large hφ hφ1.ne hR (R ^ 2 + 1),
    eventually_first_most_frequent hφ hφ1 (R := R)] with n h₁ h₂ h₃ η hη₁ hη₂
  have hη₁' : |(whiten φ n (count η 0) (count η 1) (count η 2)).1| < R := hη₁
  have hη₂' : |(whiten φ n (count η 0) (count η 1) (count η 2)).2| < R := hη₂
  have hl := h₁ _ _ _ (count_add η) hη₁' hη₂'
  have hsq := sq_lt_of_abs_lt hη₁'
  have hm₁ : min ε 1 ≤ ε := min_le_left _ _
  have hm₂ : min ε 1 ≤ 1 := min_le_right _ _
  have hline : lineS (count η 1) (count η 2) < R ^ 2 + 1 := by linarith [(abs_lt.1 hl).2]
  obtain ⟨h₆, h₇⟩ := h₂ _ _ _ (count_add η) hη₁' hη₂'
  have hfirst := h₃ _ _ _ (count_add η) hη₂'
  have ha := count_nonneg η 0
  have hb := count_nonneg η 1
  have hc := count_nonneg η 2
  have hstar₁ : lineS (count η 0) (count η 2) ≤ starS (count η 0) (count η 1) (count η 2) := by
    rw [← starS_swap]
    exact lineS_le_starS hb ha hc
  have hstar₂ : lineS (count η 0) (count η 1) ≤ starS (count η 0) (count η 1) (count η 2) := by
    rw [← starS_rot]
    exact lineS_le_starS hc ha hb
  have ht3 : t3S (count η 0) (count η 1) (count η 2) = lineS (count η 1) (count η 2) := by
    unfold t3S
    rw [ite_eq_left hfirst]
    refine min_eq_left (le_min ?_ ?_)
    · split_ifs
      · exact (hline.trans h₆).le
      · exact (hline.trans h₆).le.trans hstar₁
    · split_ifs
      · exact (hline.trans h₇).le
      · exact (hline.trans h₇).le.trans hstar₂
  change |t3S _ _ _ - (whiten φ n _ _ _).1 ^ 2| < ε
  rw [ht3]
  exact hl.trans_le hm₁

/-- Off the singularity, the tail of the T3 statistic tends to that of `χ²₁`. -/
theorem tendsto_iidProb_lt_t3S_of_lt {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) (t : ℝ) :
    Tendsto (fun n ↦ iidProb (cutPoint φ) n fun η ↦ t < t3S (count η 0) (count η 1) (count η 2)) atTop
      (𝓝 (chiSqOneTail t)) := by
  rw [← stdPlane_real_first]
  refine tendsto_iidProb_of_threshold hφ (T := fun z ↦ z.1 ^ 2) (by fun_prop) ?_ ?_ (stdPlane_first_null t)
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t3S_of_lt hφ hφ1 R hR δ hδ] with n hn η h₁ h₂ h₃
    have := (abs_lt.1 (hn η h₁ h₂)).1
    linarith
  · intro R hR δ hδ
    filter_upwards [closeOnBalls_t3S_of_lt hφ hφ1 R hR δ hδ] with n hn η h₁ h₂ h₃ h₄
    have := (abs_lt.1 (hn η h₁ h₂)).2
    linarith

/-- Off the singularity, the normal sample has a large mean, and the T3 variable is `Z²`. -/
theorem closeOnBalls_t3Var_of_lt {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) :
    CloseOnBalls (Ω := fun _ ↦ ℝ × ℝ) (fun (n : ℕ) (z : ℝ × ℝ) ↦ (z.1, z.2 - muZero φ n))
      (fun _ z ↦ t3Var φ z) (fun z ↦ z.1 ^ 2) := by
  intro R hR ε hε
  have hgap : 0 < |1 - φ| * (2 / 3) := by
    have := abs_pos.2 (sub_ne_zero.2 hφ1.ne')
    positivity
  have hsqrt : Tendsto (fun n : ℕ ↦ √(2 * (n : ℝ))) atTop atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop (3 * R / (|1 - φ| * (2 / 3)))] with n hn z hz₁ hz₂
  have hz₁' : |z.1| < R := hz₁
  have hz₂' : |z.2 - muZero φ n| < R := hz₂
  have hμ := abs_muZero_ge (m := n) hφ.1 hφ.2
  rw [abs_of_nonneg (muZero_nonneg_of_le_one hφ1.le)] at hμ
  rw [div_le_iff₀ hgap] at hn
  have hμ' : 3 * R ≤ muZero φ n := by nlinarith
  have hy : 2 * R ≤ z.2 := by linarith [(abs_lt.1 hz₂').1]
  have e : t3Var φ z = z.1 ^ 2 :=
    t3Var_eq_of_large (κ := R ^ 2) hφ1.le (sq_lt_of_abs_lt hz₁').le
      (by rw [Real.sqrt_sq hR.le]; exact hy)
  change |t3Var φ z - z.1 ^ 2| < ε
  rw [e, sub_self, abs_zero]
  exact hε

end Phylogenetics.Trinomial

namespace External.MitchellAllmanRhodes2019

open Phylogenetics Phylogenetics.Trinomial Phylogenetics.QuartetTests

/-- **Proposition 4.1** (`ext:t3_approx`) of Mitchell, Allman, Rhodes 2019, for the trinomial. At the true point
`θ₀ = (1 - 2φ/3, φ/3, φ/3)`, `0 < φ ≤ 1`, the likelihood ratio statistic of model T3 and the variable `t3Var φ`, with
`Z ~ N(0, 1)`, `Z̄ ~ N(μ₀(n), 1)` independent, converge in distribution to the same limit. That is the sense the source gives to
"approximately distributed". For `φ < 1` the limit is `χ²₁`; for `φ = 1` it is the law of `t3Var 1` under `stdPlane`, which does not
depend on `n`.

The equality of the variable with the distance to the half-lines is `QuartetTests.t3Var_eq_min_sqDistHalfLine`.

Departure from the source: it takes the first step from its Theorem 3.1 and so from van der Vaart's Theorem 16.7, on which see the
module docstring. Here it is proved for this model directly from the central limit theorem. -/
theorem proposition4_1 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≤ 1) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ t3S (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map (t3Var φ)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) := by
  rcases hφ1.eq_or_lt with rfl | hlt
  · refine ⟨⟨stdPlane.map (t3Var 1), inferInstance⟩, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        tendstoInDistribution_t3S_centroid.tendsto f
    · have hsample : ∀ n : ℕ, normalSample (muZero 1 n) = stdPlane := by
        intro n
        rw [muZero_one]
        rfl
      simp only [hsample]
      exact tendsto_const_nhds
  · have hT : Continuous fun z : ℝ × ℝ ↦ z.1 ^ 2 := by fun_prop
    have hSm : ∀ n : ℕ, AEMeasurable (fun η : Fin n → Fin 3 ↦ t3S (count η 0) (count η 1) (count η 2))
        (Measure.pi fun _ : Fin n ↦ (cutPoint_isDist hφ).toPMF.toMeasure) :=
      fun n ↦ Measurable.of_discrete.aemeasurable
    refine ⟨⟨stdPlane.map fun z ↦ z.1 ^ 2, inferInstance⟩, fun f ↦ ?_, fun f ↦ ?_⟩
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls (tendstoInDistribution_sampleW hφ) hSm hT
          (closeOnBalls_t3S_of_lt hφ hlt)).tendsto f
    · have hlaw : TendstoInDistribution (fun (n : ℕ) (z : ℝ × ℝ) ↦ (z.1, z.2 - muZero φ n)) atTop
          (fun z : ℝ × ℝ ↦ z) (fun n : ℕ ↦ normalSample (muZero φ n)) stdPlane := by
        refine ⟨fun n ↦ (by fun_prop), by fun_prop, ?_⟩
        simp only [normalSample_map_sub]
        have : stdPlane.map (fun z : ℝ × ℝ ↦ z) = stdPlane := Measure.map_id'
        simp only [this]
        exact tendsto_const_nhds
      exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
        (tendstoInDistribution_of_closeOnBalls hlaw
          (S := fun (_ : ℕ) (z : ℝ × ℝ) ↦ t3Var φ z)
          (fun n ↦ (measurable_t3Var φ).aemeasurable)
          hT (closeOnBalls_t3Var_of_lt hφ hlt)).tendsto f

end External.MitchellAllmanRhodes2019

namespace Phylogenetics.QuartetTests

open Trinomial

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}
  {sides : Γ → Finset (Finset X)}

/-! ### The statistic as a function of the three counts -/

/-- The T3 statistic through the counts of the three topologies. -/
theorem t3Stat_eq_t3S (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) : t3Stat c s.taxa = t3S (c s) (c r₁) (c r₂) := by
  obtain ⟨hs₁, hs₂, ha₁, ht₁, ht₂⟩ := alternatives_taxa hne h
  obtain ⟨-, -, ha₂, -, -⟩ := alternatives_taxa hne.symm (by rw [h, Finset.pair_comm] : s.alternatives = {r₂, r₁})
  have hstar := starStat_eq_starS c hne h
  have e₀ : t1Stat c s = if (c r₁ + c r₂) / 2 ≤ c s then lineS (c r₁) (c r₂)
      else starS (c s) (c r₁) (c r₂) := by
    unfold t1Stat
    rw [h, Finset.sum_pair hne, lineStat_eq_lineS c hne h, hstar]
  have e₁ : t1Stat c r₁ = if (c s + c r₂) / 2 ≤ c r₁ then lineS (c s) (c r₂)
      else starS (c s) (c r₁) (c r₂) := by
    unfold t1Stat
    rw [ha₁, Finset.sum_pair hs₂, lineStat_eq_lineS c hs₂ ha₁, ht₁, hstar]
  have e₂ : t1Stat c r₂ = if (c s + c r₁) / 2 ≤ c r₂ then lineS (c s) (c r₁)
      else starS (c s) (c r₁) (c r₂) := by
    unfold t1Stat
    rw [ha₂, Finset.sum_pair hs₁, lineStat_eq_lineS c hs₁ ha₂, ht₂, hstar]
  have hs : s ∈ treesOn s.taxa := mem_treesOn_taxa s
  have hr₁ : r₁ ∈ treesOn s.taxa := mem_treesOn.2 ht₁
  have hr₂ : r₂ ∈ treesOn s.taxa := mem_treesOn.2 ht₂
  have : Nonempty {t // t ∈ treesOn s.taxa} := ⟨⟨s, hs⟩⟩
  refine le_antisymm ?_ ?_
  · unfold t3S
    refine le_min ?_ (le_min ?_ ?_)
    · rw [← e₀]
      exact t3Stat_le_t1Stat c hs
    · rw [← e₁]
      exact t3Stat_le_t1Stat c hr₁
    · rw [← e₂]
      exact t3Stat_le_t1Stat c hr₂
  · refine le_ciInf ?_
    rintro ⟨t, ht⟩
    unfold t3S
    by_cases hts : t = s
    · subst hts
      simp only
      rw [e₀]
      exact min_le_left _ _
    · have hmem : t ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 ht, hts⟩
      rw [h] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · simp only
        rw [e₁]
        exact (min_le_right _ _).trans (min_le_left _ _)
      · simp only
        rw [e₂]
        exact (min_le_right _ _).trans (min_le_right _ _)

/-- **`t3Stat` is the likelihood ratio statistic** (`ext:t3_lrt`) of model T3 against the open simplex, on positive counts: the source's `Λ_n`. -/
theorem t3Stat_eq_likelihoodRatio {c : QuartetTree X → ℝ} {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (h : s.alternatives = {r₁, r₂}) (h₀ : 0 < c s) (h₁ : 0 < c r₁) (h₂ : 0 < c r₂) :
    t3Stat c s.taxa = 2 * (sSup (logLik (c s) (c r₁) (c r₂) '' openSimplex) -
      sSup (logLik (c s) (c r₁) (c r₂) '' t3Null)) := by
  rw [t3Stat_eq_t3S c hne h, t3S_eq_likelihoodRatio h₀ h₁ h₂]

/-! ### Reduction of the sample to three classes -/

/-- At the singularity, the law of the three classes is the centroid. -/
theorem pushDist_eq_centroid (hd : IsDist dist) (hs : DisplaysOne dist sides)
    {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂) (hr : s.alternatives = {r₁, r₂})
    (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) :
    pushDist dist (threeLabel sides s r₁) = cutPoint 1 := by
  obtain ⟨-, -, -, ht₁, ht₂⟩ := alternatives_taxa hne hr
  rw [pushDist_eq_cutPoint hd hs hne hr (by rw [h r₁ (mem_treesOn.2 ht₁), h r₂ (mem_treesOn.2 ht₂)]),
    h r₁ (mem_treesOn.2 ht₁)]
  norm_num

/-! ### The limit law of the statistic -/

/-- A set of four taxa is `s.taxa` for a quartet tree `s`, with its two alternatives. -/
theorem exists_tree_of_card (hq : ∀ {q : Finset X}, q.card = 4 → (treesOn q).Nonempty)
    {q : Finset X} (hc : q.card = 4) :
    ∃ s r₁ r₂ : QuartetTree X, s.taxa = q ∧ r₁ ≠ r₂ ∧ s.alternatives = {r₁, r₂} := by
  obtain ⟨s, hs⟩ := hq hc
  obtain ⟨r₁, r₂, hne, h⟩ := QuartetTree.exists_alternatives s
  exact ⟨s, r₁, r₂, mem_treesOn.1 hs, hne, h⟩

theorem treesOn_nonempty {q : Finset X} (hq : q.card = 4) : (treesOn q).Nonempty := by
  rw [← Finset.card_pos, card_treesOn hq]
  norm_num

/-- **The limit law of the T3 statistic at the singularity** (`ext:t3_limit`). At a concordance factor `(1/3, 1/3, 1/3)` on the
taxa `q`, the tail at every `t` of the T3 statistic of a sample tends to `t3Tail 1 m t`, the tail of the variable of Proposition 4.1
with `Z`, `Z̄` standard normal, for which `μ₀ = 0` whatever the sample size `m`. "Then for any sample size `n` the approximate
distribution in Equation `eq:T3dis` simplifies, with both `Z` and `Z̄` standard normal. Although this distribution is not a `χ²`, it is
exactly the asymptotic distribution" (Mitchell, Allman, Rhodes 2019, after Proposition 4.1).

Departure from the source: it reads this off its Theorem 3.1, as the tangent cone at the singularity. Here the limit comes from the
central limit theorem for the trinomial; see the module docstring. -/
theorem t3Stat_limitLaw (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X} (hq : q.card = 4)
    (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) (m t : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω => t < t3Stat (quartetCount sides ω) q) atTop
      (𝓝 (t3Tail 1 m t)) := by
  obtain ⟨s, r₁, r₂, rfl, hne, hr⟩ := exists_tree_of_card treesOn_nonempty hq
  have hp := pushDist_eq_centroid hd hs hne hr h
  have := tendsto_iidProb_lt_t3S_centroid m t
  rw [← hp] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_three_counts hs hne hr n (fun a b c ↦ t < t3S a b c)]
  simp only [t3Stat_eq_t3S _ hne hr]

/-- **Off the singularity, the limit law of the T3 statistic is `χ²₁`** (`ext:t3_approx`). At a concordance factor strictly on a
half-line, with positive probabilities, the tail at every `t` of the T3 statistic of a sample tends to that of `χ²₁`: "It follows that
`Λ̃_n` is asymptotically `χ²₁`-distributed as is the likelihood ratio statistic `Λ_n`" (Mitchell, Allman, Rhodes 2019, after
Proposition 4.1). -/
theorem t3Stat_limitLaw_of_isT1Strict (hd : IsDist dist) (hs : DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r ∈ s.alternatives, 0 < displayCF dist sides r) (t : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω => t < t3Stat (quartetCount sides ω) s.taxa) atTop
      (𝓝 (chiSqOneTail t)) := by
  obtain ⟨r₁, r₂, hne, hr⟩ := QuartetTree.exists_alternatives s
  have hm₁ : r₁ ∈ s.alternatives := by rw [hr]; simp
  have hm₂ : r₂ ∈ s.alternatives := by rw [hr]; simp
  have heq := hstrict.2 r₁ hm₁ r₂ hm₂
  have hsum := sum_displayCF_treesOn hd hs s.card_taxa
  rw [sum_treesOn _ hne hr, ← heq] at hsum
  have hlt := hstrict.1 r₁ hm₁
  have hq0 := hpos r₁ hm₁
  have hφ : 0 < 3 * displayCF dist sides r₁ ∧ 3 * displayCF dist sides r₁ < 3 / 2 := by
    constructor <;> linarith
  have hφ1 : 3 * displayCF dist sides r₁ < 1 := by linarith
  have := tendsto_iidProb_lt_t3S_of_lt hφ hφ1 t
  rw [← pushDist_eq_cutPoint hd hs hne hr heq] at this
  refine this.congr fun n ↦ ?_
  rw [← iidProb_three_counts hs hne hr n (fun a b c ↦ t < t3S a b c)]
  simp only [t3Stat_eq_t3S _ hne hr]

/-- `t3Stat_limitLaw` as a theorem on distribution functions, with the density of Proposition 4.2 (`ext:t3_limit`): at every `t` the
probability that the T3 statistic of a sample at the singularity is at most `t` tends to the integral of the density up to `t`. The
density is `3 / (2 √(2 π λ)) exp (-λ / 2) (1 - erf √(λ / 6))` on `λ > 0`, by `t3Density_one`. -/
theorem t3Stat_limitLaw_density (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) (t : ℝ) :
    Tendsto (fun n => iidProb dist n fun ω => t3Stat (quartetCount sides ω) q ≤ t) atTop
      (𝓝 (∫ v in Iic t, t3Density 1 0 v)) := by
  rw [← one_sub_t3Tail_eq_integral (φ := 1) (by norm_num)]
  refine ((tendsto_const_nhds (x := (1 : ℝ))).sub (t3Stat_limitLaw hd hs hq h 0 t)).congr fun n ↦ ?_
  rw [← iidProb_not hd]
  simp only [not_lt]

/-- A p-value read from the tail of the limit law of a statistic is asymptotically uniform. -/
theorem asymptoticallyUniform_of_tendsto_tail (hd : IsDist dist) {S : ∀ n, (Fin n → Γ) → ℝ} {G : ℝ → ℝ}
    (hanti : Antitone G) (hpos : ∀ n ω, 0 < G (S n ω)) (hsurj : ∀ x, 0 < x → x ≤ 1 → ∃ t, G t = x)
    (hlim : ∀ t, Tendsto (fun n => iidProb dist n fun ω => t < S n ω) atTop (𝓝 (G t))) :
    AsymptoticallyUniform dist fun n ω => G (S n ω) := by
  intro x h0 h1
  rcases h0.eq_or_lt with rfl | hx
  · have hz : ∀ n : ℕ, iidProb dist n (fun ω => G (S n ω) ≤ 0) = 0 := fun n =>
      Finset.sum_eq_zero fun ω _ => ite_eq_right fun hle => absurd hle (not_le.2 (hpos n ω))
    simp only [hz]
    exact tendsto_const_nhds
  obtain ⟨t, ht⟩ := hsurj x hx h1
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hl := hlim t
    rw [ht] at hl
    filter_upwards [hl.eventually (lt_mem_nhds ha)] with n hn
    refine hn.trans_le (iidProb_mono hd fun ω hω => ?_)
    rw [← ht]
    exact hanti hω.le
  · by_cases ha1 : 1 < a
    · exact Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha1
    obtain ⟨t', ht'⟩ := hsurj ((x + a) / 2) (by linarith) (by linarith [not_lt.1 ha1])
    have hl := hlim t'
    rw [ht'] at hl
    filter_upwards [hl.eventually (gt_mem_nhds (by linarith : (x + a) / 2 < a))] with n hn
    refine (iidProb_mono hd fun ω hω => ?_).trans_lt hn
    by_contra hle
    have := hanti (not_lt.1 hle)
    rw [ht'] at this
    linarith

/-- **The p-value with the true parameter at the singularity is asymptotically uniform** (`ext:t3_pvalue_true`). "At the singularity the `χ²₁` distribution is
not the asymptotic distribution, while that of Equation `eq:T3pdf` is": this is what the source's simulations at `μ₀ = 0` look at,
"by numerical integration from the observed value of the statistic to infinity" (Mitchell, Allman, Rhodes 2019, Section 4), with
the true `μ₀ = 0` and no estimate of it. It does not say this of the p-value `t3PValue`, which uses the maximum likelihood estimate. -/
theorem t3Tail_t3Stat_asymptoticallyUniform (hd : IsDist dist) (hs : DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) (m : ℝ) :
    AsymptoticallyUniform dist fun _ ω => t3Tail 1 m (t3Stat (quartetCount sides ω) q) :=
  asymptoticallyUniform_of_tendsto_tail hd (G := t3Tail 1 m)
    (S := fun _ ω => t3Stat (quartetCount sides ω) q)
    (fun _ _ hst => t3Tail_anti 1 m hst)
    (fun _ ω => t3Tail_pos (φ := 1) zero_le_one le_rfl
      (t3Stat_nonneg (quartetCount_nonneg (sides := sides) ω) hq))
    (fun _ hx hx1 => (exists_t3Tail_eq (φ := 1) le_rfl m hx hx1).imp fun _ ht => ht.2)
    (t3Stat_limitLaw hd hs hq h m)

/-- The law of the T3 statistic of a sample is that of the trinomial statistic on the three counts, at the singularity. -/
theorem map_t3Stat_eq [MeasurableSpace Γ] [MeasurableSingletonClass Γ] (hd : IsDist dist)
    (hs : DisplaysOne dist sides) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (hr : s.alternatives = {r₁, r₂}) (h : ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3) (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure).map
        (fun ω ↦ t3Stat (quartetCount sides ω) s.taxa) =
      (Measure.pi fun _ : Fin n ↦ (cutPoint_isDist one_mem_cutRange).toPMF.toMeasure).map
        (fun η ↦ t3S (count η 0) (count η 1) (count η 2)) := by
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply Measurable.of_discrete hA, Measure.map_apply Measurable.of_discrete hA]
  have h₁ := iidProb_eq_pi hd n (fun ω ↦ t3Stat (quartetCount sides ω) s.taxa ∈ A)
  have h₂ := iidProb_eq_pi (cutPoint_isDist one_mem_cutRange) n
    (fun η ↦ t3S (count η 0) (count η 1) (count η 2) ∈ A)
  have h₃ := iidProb_three_counts hs hne hr n (fun a b c ↦ t3S a b c ∈ A)
  rw [pushDist_eq_centroid hd hs hne hr h] at h₃
  simp only [← t3Stat_eq_t3S _ hne hr] at h₃
  rw [h₁, h₂] at h₃
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h₃

/-- `t3Stat_limitLaw` as convergence in distribution (`ext:t3_limit`), for the law of a sample as a product measure. -/
theorem tendstoInDistribution_t3Stat [MeasurableSpace Γ] [MeasurableSingletonClass Γ] (hd : IsDist dist)
    (hs : DisplaysOne dist sides) {q : Finset X} (hq : q.card = 4)
    (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) :
    TendstoInDistribution (fun (n : ℕ) (ω : Fin n → Γ) ↦ t3Stat (quartetCount sides ω) q) atTop
      (t3Var 1) (fun n ↦ Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure) stdPlane := by
  obtain ⟨s, r₁, r₂, rfl, hne, hr⟩ := exists_tree_of_card treesOn_nonempty hq
  refine ⟨fun n ↦ Measurable.of_discrete.aemeasurable, (measurable_t3Var 1).aemeasurable, ?_⟩
  exact tendstoInDistribution_t3S_centroid.tendsto.congr fun n ↦
    Subtype.ext (map_t3Stat_eq hd hs hne hr h n).symm

/-! ### The limit is not a `χ²` -/

/-- The law `χ²_d`: that of the sum of the squares of `d` independent standard normals. -/
def chiSqLaw (d : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin d => gaussianReal 0 1).map fun z => ∑ i, z i ^ 2

/-- The tail of `χ²_d`, for `d ≥ 1`, is at least that of `χ²₁`. -/
theorem chiSqOneTail_le_chiSqLaw {d : ℕ} (hd : 0 < d) (t : ℝ) :
    chiSqOneTail t ≤ (chiSqLaw d).real (Ioi t) := by
  have hm : Measurable fun z : Fin d → ℝ => ∑ i, z i ^ 2 := by fun_prop
  have hset : MeasurableSet {x : ℝ | t < x ^ 2} := measurableSet_lt measurable_const (by fun_prop)
  rw [chiSqLaw, map_measureReal_apply hm measurableSet_Ioi, chiSqOneTail]
  have hpres := (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) (⟨0, hd⟩ : Fin d))
  have e := hpres.measure_preimage hset.nullMeasurableSet
  rw [measureReal_def, ← e, ← measureReal_def]
  refine measureReal_mono fun z hz => ?_
  have hz' : t < z ⟨0, hd⟩ ^ 2 := hz
  have hle : z ⟨0, hd⟩ ^ 2 ≤ ∑ i, z i ^ 2 :=
    Finset.single_le_sum (f := fun i => z i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  exact hz'.trans_le hle

/-- At the singularity, the distance to the three half-lines has more mass near `0` than `Z²`: its density in the distance is
`3 φ(u) (1 - erf (u / √6))`, against `2 φ(u)`. So the tail of the limit law is below that of `χ²₁`, at small `t`. -/
theorem exists_t3Tail_lt_chiSqOneTail (m : ℝ) : ∃ t : ℝ, 0 < t ∧ t3Tail 1 m t < chiSqOneTail t := by
  have hα : (Real.pi / 6) ∈ Ioo 0 (Real.pi / 2) := ⟨by positivity, by linarith [Real.pi_pos]⟩
  set k : ℝ := 1 / √3 with hk
  have hk0 : 0 < k := by positivity
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < √3 := by positivity
  have hk₁ : Real.cos (Real.pi / 6) / (1 + Real.sin (Real.pi / 6)) = k := by
    rw [Real.cos_pi_div_six, Real.sin_pi_div_six, hk]
    field_simp
    nlinarith
  have hk₂ : Real.sin (Real.pi / 6) / Real.cos (Real.pi / 6) = k := by
    rw [Real.cos_pi_div_six, Real.sin_pi_div_six, hk]
    field_simp
  -- `erf (k √t / √2)` is small for small `t`
  have hcont : Continuous fun t : ℝ => Real.erf (k * √t / √2) := by
    have := Real.continuous_erf
    fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Real.erf (k * √t / √2) < 1 / 3 :=
    hcont.continuousAt.eventually_lt_const (by simp [erf_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set t := δ / 2 with ht
  have ht0 : 0 < t := by positivity
  have hsm : Real.erf (k * √t / √2) < 1 / 3 := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    linarith
  refine ⟨t, ht0, ?_⟩
  set e := Real.erf (k * √t / √2) with he
  -- the lower bound of the density on `(0, √t]`
  have hbound : ∀ u ∈ Ioc 0 √t, 3 * (1 - e) * gaussianPDFReal 0 1 u ≤
      T3Pdf.distDensity (Real.sin (Real.pi / 6)) (Real.cos (Real.pi / 6)) 0 u := by
    intro u hu
    have herf : Real.erf ((k * u - 0) / √2) ≤ e := by
      refine Real.monotone_erf ?_
      rw [sub_zero]
      gcongr
      exact hu.2
    have herf' : Real.erf ((k * u - 0) / √2) ≤ e := herf
    simp only [T3Pdf.distDensity, hk₁, hk₂, mul_zero, neg_zero, stripDensity]
    have hp := gaussianPDFReal_nonneg 0 1 u
    nlinarith [mul_le_mul_of_nonneg_left herf' hp]
  have hP := T3Pdf.measure_halfLineDist_le hα 0 t
  have hmono : ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (3 * (1 - e) * gaussianPDFReal 0 1 u) ≤
      normalSample 0 {z | halfLineDist (Real.sin (Real.pi / 6)) (Real.cos (Real.pi / 6)) z ≤ t} := by
    rw [hP]
    exact setLIntegral_mono' measurableSet_Ioc fun u hu => ENNReal.ofReal_le_ofReal (hbound u hu)
  have hC : 0 ≤ 3 * (1 - e) := by linarith
  have hgauss : ∫⁻ u in Ioc 0 √t, ENNReal.ofReal (3 * (1 - e) * gaussianPDFReal 0 1 u) =
      ENNReal.ofReal (3 * (1 - e)) * gaussianReal 0 1 (Ioc 0 √t) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Ioc,
      ← lintegral_const_mul _ (measurable_gaussianPDF 0 1)]
    refine lintegral_congr fun u => ?_
    rw [ENNReal.ofReal_mul hC]
    rfl
  rw [hgauss, Real.sin_pi_div_six, Real.cos_pi_div_six] at hmono
  -- to real numbers
  have hIoc : (gaussianReal 0 1).real (Ioc 0 √t) = 1 / 2 * Real.erf (√t / √2) := by
    have hu : Ioi (0 : ℝ) = Ioc 0 √t ∪ Ioi √t := (Ioc_union_Ioi_eq_Ioi (Real.sqrt_nonneg t)).symm
    have hd : Disjoint (Ioc 0 √t) (Ioi √t) := Set.Ioc_disjoint_Ioi le_rfl
    have h₁ := measureReal_union (μ := gaussianReal 0 1) hd measurableSet_Ioi
    rw [← hu, gaussianReal_real_Ioi, gaussianReal_real_Ioi] at h₁
    simp only [sub_zero, zero_div, erf_zero] at h₁
    linarith
  have hreal : 3 * (1 - e) * (1 / 2 * Real.erf (√t / √2)) ≤
      stdPlane.real {z | halfLineDist (1 / 2) (√3 / 2) z ≤ t} := by
    rw [← hIoc, ← ENNReal.toReal_ofReal hC, measureReal_def, ← ENNReal.toReal_mul, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmono
  have hm : MeasurableSet {z | halfLineDist (1 / 2) (√3 / 2) z ≤ t} :=
    measurableSet_le (continuous_halfLineDist sq_add_sq_centroid).measurable measurable_const
  have hcompl : stdPlane.real {z | t < halfLineDist (1 / 2) (√3 / 2) z} =
      1 - stdPlane.real {z | halfLineDist (1 / 2) (√3 / 2) z ≤ t} := by
    rw [← probReal_compl_eq_one_sub hm]
    congr 1
    ext z
    simp
  have hchi := chiSqOneTail_eq_erf ht0.le
  have hEpos : 0 < Real.erf (√t / √2) := by
    have h₁ := chiSqOneTail_lt_of_lt le_rfl ht0
    rw [chiSqOneTail_zero, hchi] at h₁
    linarith
  rw [t3Tail_one_eq, hcompl, hchi]
  nlinarith

/-- **"This distribution is not a `χ²`"** (`ext:t3_not_chisq`) (Mitchell, Allman, Rhodes 2019, after Proposition 4.1). The limit law of the T3 statistic at
the singularity is not `χ²_d`, for any number `d ≥ 1` of degrees of freedom: at small `t` its tail is below that of `χ²₁`, and that is
at most the tail of `χ²_d`. -/
theorem map_t3Var_one_ne_chiSqLaw {d : ℕ} (hd : 0 < d) : stdPlane.map (t3Var 1) ≠ chiSqLaw d := by
  intro he
  obtain ⟨t, -, ht⟩ := exists_t3Tail_lt_chiSqOneTail 0
  have h₁ := chiSqOneTail_le_chiSqLaw hd t
  rw [← he, map_measureReal_apply (measurable_t3Var 1) measurableSet_Ioi] at h₁
  have h₂ : t3Tail 1 0 t = stdPlane.real (t3Var 1 ⁻¹' Ioi t) := by
    rw [t3Tail, muZero_one]
    rfl
  linarith

end Phylogenetics.QuartetTests
