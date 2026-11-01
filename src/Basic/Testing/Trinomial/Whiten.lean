module

public import Basic.Testing.Trinomial.CLT
public import Basic.ForMathlib.Probability.Transfer
public import Basic.Testing.Trinomial.Statistics

/-!
# The whitened frequencies of a trinomial sample at a point of the cut model

For the point `(1 - 2φ/3, φ/3, φ/3)`, `0 < φ < 3/2`, of the cut model and counts `a`, `b`, `c`, the
vector `whiten φ n a b c` is `(√(3/(2φ)) (b - c), √(1/(2φ(3 - 2φ))) (3a - n(3 - 2φ))) / √n`, the
frequencies in the coordinates of Allman, Baños, Mitchell, Rhodes (2024, Appendix C.2: Algorithms Mol.
Biol. 19, 23), centred at the generating point.

* `tendstoInDistribution_sampleW`: under sampling, it converges to two independent standard normals.
* `whiten_counts`: it determines the counts, so the statistics are functions of it.
* the `eventually_*` lemmas: the limits of the statistics in terms of it, uniformly on bounded sets.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory Filter Topology Real
open scoped Classical

namespace Phylogenetics.Trinomial

/-- The point `(1 - 2φ/3, φ/3, φ/3)` of the cut model. -/
def cutPoint (φ : ℝ) : Fin 3 → ℝ := fun i ↦ if i = 0 then 1 - 2 * φ / 3 else φ / 3

@[simp] theorem cutPoint_zero (φ : ℝ) : cutPoint φ 0 = 1 - 2 * φ / 3 := rfl
@[simp] theorem cutPoint_one (φ : ℝ) : cutPoint φ 1 = φ / 3 := rfl
@[simp] theorem cutPoint_two (φ : ℝ) : cutPoint φ 2 = φ / 3 := rfl

variable {φ : ℝ}

theorem cutPoint_isDist (hφ : 0 < φ ∧ φ < 3 / 2) : IsDist (cutPoint φ) := by
  constructor
  · intro i
    fin_cases i
    · change 0 ≤ 1 - 2 * φ / 3
      linarith [hφ.2]
    · change 0 ≤ φ / 3
      linarith [hφ.1]
    · change 0 ≤ φ / 3
      linarith [hφ.1]
  · simp only [Fin.sum_univ_three, cutPoint_zero, cutPoint_one, cutPoint_two]
    ring

/-- The standard deviation of the difference of the two alternatives in one draw. -/
def scaleA (φ : ℝ) : ℝ := √(2 * φ / 3)

/-- The standard deviation of the indicator of the first topology in one draw. -/
def scaleB (φ : ℝ) : ℝ := √(2 * φ * (3 - 2 * φ)) / 3

theorem scaleA_pos (hφ : 0 < φ ∧ φ < 3 / 2) : 0 < scaleA φ := by
  have := hφ.1
  unfold scaleA
  positivity

theorem scaleB_pos (hφ : 0 < φ ∧ φ < 3 / 2) : 0 < scaleB φ := by
  have := hφ.1
  have : 0 < 3 - 2 * φ := by linarith [hφ.2]
  unfold scaleB
  positivity

theorem scaleA_sq (hφ : 0 < φ ∧ φ < 3 / 2) : scaleA φ ^ 2 = 2 * φ / 3 := by
  unfold scaleA
  exact Real.sq_sqrt (by linarith [hφ.1])

theorem scaleB_sq (hφ : 0 < φ ∧ φ < 3 / 2) : scaleB φ ^ 2 = 2 * φ * (3 - 2 * φ) / 9 := by
  have h : 0 ≤ 2 * φ * (3 - 2 * φ) := by
    have := hφ.1
    have : 0 < 3 - 2 * φ := by linarith [hφ.2]
    positivity
  unfold scaleB
  rw [div_pow, Real.sq_sqrt h]
  norm_num

/-- The number of the draws in a given class. -/
def count {n : ℕ} (η : Fin n → Fin 3) (i : Fin 3) : ℝ :=
  ((univ.filter fun k ↦ η k = i).card : ℝ)

theorem count_nonneg {n : ℕ} (η : Fin n → Fin 3) (i : Fin 3) : 0 ≤ count η i := Nat.cast_nonneg _

theorem sum_comp_eq_count {n : ℕ} (η : Fin n → Fin 3) (f : Fin 3 → ℝ) :
    ∑ k, f (η k) = count η 0 * f 0 + count η 1 * f 1 + count η 2 * f 2 := by
  have h : ∀ j : Fin 3, ∑ k ∈ univ.filter (fun k ↦ η k = j), f (η k) = count η j * f j := by
    intro j
    rw [Finset.sum_congr rfl (g := fun _ ↦ f j)]
    · simp [count]
    · intro k hk
      rw [(Finset.mem_filter.1 hk).2]
  rw [← Finset.sum_fiberwise univ η, Fin.sum_univ_three, h, h, h]

theorem count_add {n : ℕ} (η : Fin n → Fin 3) : count η 0 + count η 1 + count η 2 = n := by
  have := sum_comp_eq_count η (fun _ ↦ 1)
  simpa using this.symm

/-- The whitened frequencies. -/
def whiten (φ : ℝ) (n : ℕ) (a b c : ℝ) : ℝ × ℝ :=
  ((√(n : ℝ))⁻¹ * ((b - c) / scaleA φ), (√(n : ℝ))⁻¹ * ((a - n * (1 - 2 * φ / 3)) / scaleB φ))

/-- The whitened frequencies of a sample. -/
def sampleW (φ : ℝ) {n : ℕ} (η : Fin n → Fin 3) : ℝ × ℝ :=
  whiten φ n (count η 0) (count η 1) (count η 2)

private def aFun (φ : ℝ) : Fin 3 → ℝ := fun i ↦
  if i = 0 then 0 else if i = 1 then 1 / scaleA φ else -1 / scaleA φ

private def bFun (φ : ℝ) : Fin 3 → ℝ := fun i ↦
  if i = 0 then (2 * φ / 3) / scaleB φ else -(1 - 2 * φ / 3) / scaleB φ

private lemma sum_aFun {n : ℕ} (η : Fin n → Fin 3) :
    ∑ k, aFun φ (η k) = (count η 1 - count η 2) / scaleA φ := by
  rw [sum_comp_eq_count]
  simp only [aFun]
  simp
  ring

private lemma sum_bFun {n : ℕ} (η : Fin n → Fin 3) :
    ∑ k, bFun φ (η k) = (count η 0 - n * (1 - 2 * φ / 3)) / scaleB φ := by
  rw [sum_comp_eq_count]
  simp only [bFun]
  have h := count_add η
  simp
  rw [← h]
  ring

/-- The first `n` coordinates of the independent sequence have the finite product law. -/
theorem iidSeq_map_restrict {Γ : Type*} [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    {dist : Γ → ℝ} (hd : IsDist dist) (n : ℕ) :
    (iidSeq dist hd).map (fun (ω : ℕ → Γ) (i : Fin n) ↦ ω i) =
      Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure := by
  have hm : Measurable fun (ω : ℕ → Γ) (i : Fin n) ↦ ω i := by fun_prop
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply hm hA]
  have h₁ := iidProb_eq_iidSeq hd n (fun η ↦ η ∈ A)
  have h₂ := iidProb_eq_pi hd n (fun η ↦ η ∈ A)
  rw [h₁] at h₂
  have hpi : IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure) := inferInstance
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h₂

/-- **The central limit theorem for the whitened frequencies.** -/
theorem tendstoInDistribution_sampleW (hφ : 0 < φ ∧ φ < 3 / 2) :
    TendstoInDistribution (fun (n : ℕ) (η : Fin n → Fin 3) ↦ sampleW φ η) atTop (fun z : ℝ × ℝ ↦ z)
      (fun n ↦ Measure.pi fun _ : Fin n ↦ (cutPoint_isDist hφ).toPMF.toMeasure) stdPlane := by
  have hd := cutPoint_isDist hφ
  have hA := scaleA_pos hφ
  have hB := scaleB_pos hφ
  have hA2 := scaleA_sq hφ
  have hB2 := scaleB_sq hφ
  have hb0 : (3 - 2 * φ) ≠ 0 := by linarith [hφ.2]
  have hφ0 := hφ.1.ne'
  have base := tendstoInDistribution_normalizedSums hd (aFun φ) (bFun φ)
    (by
      simp only [Fin.sum_univ_three, aFun, cutPoint_zero, cutPoint_one, cutPoint_two]
      simp
      ring)
    (by
      simp only [Fin.sum_univ_three, bFun, cutPoint_zero, cutPoint_one, cutPoint_two]
      simp
      ring)
    (by
      simp only [Fin.sum_univ_three, aFun, cutPoint_zero, cutPoint_one, cutPoint_two]
      simp
      have : scaleA φ ≠ 0 := hA.ne'
      field_simp
      rw [hA2]
      field_simp
      ring)
    (by
      simp only [Fin.sum_univ_three, bFun, cutPoint_zero, cutPoint_one, cutPoint_two]
      simp
      have : scaleB φ ≠ 0 := hB.ne'
      field_simp
      rw [hB2]
      field_simp
      ring)
    (by
      simp only [Fin.sum_univ_three, aFun, bFun, cutPoint_zero, cutPoint_one, cutPoint_two]
      simp
      ring)
  refine ⟨fun n ↦ Measurable.of_discrete.aemeasurable, by fun_prop, ?_⟩
  have hlaw : ∀ n : ℕ, (Measure.pi fun _ : Fin n ↦ hd.toPMF.toMeasure).map (sampleW φ) =
      (iidSeq (cutPoint φ) hd).map fun ω : ℕ → Fin 3 ↦
        ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, aFun φ (ω k),
          (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, bFun φ (ω k)) := by
    intro n
    have hm : Measurable fun (ω : ℕ → Fin 3) (i : Fin n) ↦ ω i := by fun_prop
    rw [← iidSeq_map_restrict hd n, Measure.map_map Measurable.of_discrete hm]
    congr 1
    funext ω
    simp only [Function.comp, sampleW, whiten]
    rw [← sum_aFun (φ := φ), ← sum_bFun (φ := φ), Finset.sum_range, Finset.sum_range]
  have := base.tendsto
  simp only [← hlaw] at this
  exact this

/-- The counts in terms of the whitened frequencies. -/
theorem whiten_counts (hφ : 0 < φ ∧ φ < 3 / 2) {n : ℕ} (hn : 0 < n) {a b c : ℝ}
    (hsum : a + b + c = n) :
    a = (1 - 2 * φ / 3) * n + √(n : ℝ) * (scaleB φ * (whiten φ n a b c).2) ∧
    b = φ / 3 * n + √(n : ℝ) *
      ((scaleA φ * (whiten φ n a b c).1 - scaleB φ * (whiten φ n a b c).2) / 2) ∧
    c = φ / 3 * n + √(n : ℝ) *
      ((-(scaleA φ * (whiten φ n a b c).1) - scaleB φ * (whiten φ n a b c).2) / 2) := by
  have hA := (scaleA_pos hφ).ne'
  have hB := (scaleB_pos hφ).ne'
  have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have h₁ : √(n : ℝ) * (scaleA φ * (whiten φ n a b c).1) = b - c := by
    simp only [whiten]
    field_simp
  have h₂ : √(n : ℝ) * (scaleB φ * (whiten φ n a b c).2) = a - n * (1 - 2 * φ / 3) := by
    simp only [whiten]
    field_simp
  generalize scaleA φ * (whiten φ n a b c).1 = x at *
  generalize scaleB φ * (whiten φ n a b c).2 = y at *
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -h₂
  · linear_combination (-1 / 2) * h₁ + (1 / 2) * h₂ + (1 / 2) * hsum
  · linear_combination (1 / 2) * h₁ + (1 / 2) * h₂ + (1 / 2) * hsum

/-! ### The statistics in terms of the whitened frequencies -/

private lemma abs_mul_le {A B R x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : |x| < R) :
    |A * x| ≤ (A + B) * R := by
  rw [abs_mul, abs_of_pos hA]
  have hR : 0 < R := (abs_nonneg x).trans_lt hx
  nlinarith

private lemma abs_half_le {A B R x y : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : |x| < R) (hy : |y| < R) :
    |(A * x - B * y) / 2| ≤ (A + B) * R ∧ |(-(A * x) - B * y) / 2| ≤ (A + B) * R := by
  have h₁ := abs_le.1 (abs_mul_le (A := A) (B := B) hA hB hx)
  have h₂ := abs_le.1 (abs_mul_le (A := B) (B := A) hB hA hy)
  rw [add_comm B A] at h₂
  have hR : 0 < R := (abs_nonneg x).trans_lt hx
  have hp : 0 ≤ (A + B) * R := by positivity
  constructor <;> rw [abs_le] <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

variable {R ε : ℝ}

/-- The line of the first topology: its statistic is the square of the first whitened coordinate. -/
theorem eventually_lineS_first (hφ : 0 < φ ∧ φ < 3 / 2) (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).1| < R →
      |(whiten φ n a b c).2| < R → |lineS b c - (whiten φ n a b c).1 ^ 2| < ε := by
  have hA := scaleA_pos hφ
  have hB := scaleB_pos hφ
  have hα : 0 < φ / 3 := by linarith [hφ.1]
  filter_upwards [eventually_lineS_close hα (by positivity : 0 < (scaleA φ + scaleB φ) * R) hε,
    eventually_gt_atTop 0] with n hn hn0 a b c hsum h₁ h₂
  obtain ⟨-, hb, hc⟩ := whiten_counts hφ hn0 hsum
  obtain ⟨hf, hg⟩ := abs_half_le hA hB h₁ h₂
  have := hn _ _ hf hg
  rw [← hb, ← hc] at this
  have hA2 := scaleA_sq hφ
  have hφ0 := hφ.1.ne'
  have e : ((scaleA φ * (whiten φ n a b c).1 - scaleB φ * (whiten φ n a b c).2) / 2 -
      (-(scaleA φ * (whiten φ n a b c).1) - scaleB φ * (whiten φ n a b c).2) / 2) ^ 2 / (2 * (φ / 3)) =
      (whiten φ n a b c).1 ^ 2 := by
    generalize (whiten φ n a b c).1 = x
    generalize (whiten φ n a b c).2 = y
    rw [show (scaleA φ * x - scaleB φ * y) / 2 - (-(scaleA φ * x) - scaleB φ * y) / 2 = scaleA φ * x by
      ring, mul_pow, hA2]
    field_simp
  rwa [e] at this

/-- Off the centroid, the lines of the other two topologies have large statistics. -/
theorem eventually_lineS_other_large (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≠ 1) (hR : 0 < R) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).1| < R →
      |(whiten φ n a b c).2| < R → K < lineS a c ∧ K < lineS a b := by
  have hA := scaleA_pos hφ
  have hB := scaleB_pos hφ
  have hα : 0 < 1 - 2 * φ / 3 := by linarith [hφ.2]
  have hβ : 0 < φ / 3 := by linarith [hφ.1]
  have hne : 1 - 2 * φ / 3 ≠ φ / 3 := by
    intro h
    apply hφ1
    linarith
  filter_upwards [eventually_lineS_large hα hβ hne (by positivity : 0 < (scaleA φ + scaleB φ) * R) K,
    eventually_gt_atTop 0] with n hn hn0 a b c hsum h₁ h₂
  obtain ⟨ha, hb, hc⟩ := whiten_counts hφ hn0 hsum
  obtain ⟨hf, hg⟩ := abs_half_le hA hB h₁ h₂
  have hf₀ := abs_mul_le (A := scaleB φ) (B := scaleA φ) hB hA h₂
  rw [add_comm (scaleB φ)] at hf₀
  have h₃ := hn _ _ hf₀ hg
  have h₄ := hn _ _ hf₀ hf
  rw [← ha, ← hc] at h₃
  rw [← ha, ← hb] at h₄
  exact ⟨h₃, h₄⟩

private lemma scale_mul_one : scaleA 1 * scaleB 1 = 2 * √3 / 9 := by
  have h₁ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  have hA := scaleA_pos h₁
  have hB := scaleB_pos h₁
  have hA2 := scaleA_sq h₁
  have hB2 := scaleB_sq h₁
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √3 := by positivity
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [mul_pow, hA2, hB2, div_pow, mul_pow, h3]
  norm_num

/-- At the centroid, the line of the second topology. -/
theorem eventually_lineS_second_centroid (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten 1 n a b c).1| < R →
      |(whiten 1 n a b c).2| < R →
      |lineS a c - (1 / 2 * (whiten 1 n a b c).1 + √3 / 2 * (whiten 1 n a b c).2) ^ 2| < ε := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  have hA := scaleA_pos hφ
  have hB := scaleB_pos hφ
  filter_upwards [eventually_lineS_close (α := 1 / 3) (by norm_num)
    (by positivity : 0 < (scaleA 1 + scaleB 1) * R) hε, eventually_gt_atTop 0]
    with n hn hn0 a b c hsum h₁ h₂
  obtain ⟨ha, -, hc⟩ := whiten_counts hφ hn0 hsum
  obtain ⟨-, hg⟩ := abs_half_le hA hB h₁ h₂
  have hf₀ := abs_mul_le (A := scaleB 1) (B := scaleA 1) hB hA h₂
  rw [add_comm (scaleB 1)] at hf₀
  have := hn _ _ hf₀ hg
  rw [show (1 / 3 : ℝ) * n = (1 - 2 * 1 / 3) * n by ring, ← ha,
    show (1 - 2 * 1 / 3 : ℝ) * n = 1 / 3 * n by ring, ← hc] at this
  have hA2 := scaleA_sq hφ
  have hB2 := scaleB_sq hφ
  have hm := scale_mul_one
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : (scaleB 1 * (whiten 1 n a b c).2 -
      (-(scaleA 1 * (whiten 1 n a b c).1) - scaleB 1 * (whiten 1 n a b c).2) / 2) ^ 2 / (2 * (1 / 3)) =
      (1 / 2 * (whiten 1 n a b c).1 + √3 / 2 * (whiten 1 n a b c).2) ^ 2 := by
    generalize (whiten 1 n a b c).1 = x
    generalize (whiten 1 n a b c).2 = y
    have hexp : (scaleB 1 * y - (-(scaleA 1 * x) - scaleB 1 * y) / 2) ^ 2 =
        (scaleA 1 ^ 2 * x ^ 2 + 6 * (scaleA 1 * scaleB 1) * (x * y) +
          9 * (scaleB 1 ^ 2 * y ^ 2)) / 4 := by
      ring
    rw [hexp, hA2, hB2, hm]
    ring_nf
    rw [h3]
    ring
  rwa [e] at this

/-- At the centroid, the line of the third topology. -/
theorem eventually_lineS_third_centroid (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten 1 n a b c).1| < R →
      |(whiten 1 n a b c).2| < R →
      |lineS a b - (1 / 2 * (whiten 1 n a b c).1 - √3 / 2 * (whiten 1 n a b c).2) ^ 2| < ε := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  have hA := scaleA_pos hφ
  have hB := scaleB_pos hφ
  filter_upwards [eventually_lineS_close (α := 1 / 3) (by norm_num)
    (by positivity : 0 < (scaleA 1 + scaleB 1) * R) hε, eventually_gt_atTop 0]
    with n hn hn0 a b c hsum h₁ h₂
  obtain ⟨ha, hb, -⟩ := whiten_counts hφ hn0 hsum
  obtain ⟨hf, -⟩ := abs_half_le hA hB h₁ h₂
  have hf₀ := abs_mul_le (A := scaleB 1) (B := scaleA 1) hB hA h₂
  rw [add_comm (scaleB 1)] at hf₀
  have := hn _ _ hf₀ hf
  rw [show (1 / 3 : ℝ) * n = (1 - 2 * 1 / 3) * n by ring, ← ha,
    show (1 - 2 * 1 / 3 : ℝ) * n = 1 / 3 * n by ring, ← hb] at this
  have hA2 := scaleA_sq hφ
  have hB2 := scaleB_sq hφ
  have hm := scale_mul_one
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : (scaleB 1 * (whiten 1 n a b c).2 -
      (scaleA 1 * (whiten 1 n a b c).1 - scaleB 1 * (whiten 1 n a b c).2) / 2) ^ 2 / (2 * (1 / 3)) =
      (1 / 2 * (whiten 1 n a b c).1 - √3 / 2 * (whiten 1 n a b c).2) ^ 2 := by
    generalize (whiten 1 n a b c).1 = x
    generalize (whiten 1 n a b c).2 = y
    have hexp : (scaleB 1 * y - (scaleA 1 * x - scaleB 1 * y) / 2) ^ 2 =
        (scaleA 1 ^ 2 * x ^ 2 - 6 * (scaleA 1 * scaleB 1) * (x * y) +
          9 * (scaleB 1 ^ 2 * y ^ 2)) / 4 := by
      ring
    rw [hexp, hA2, hB2, hm]
    ring_nf
    rw [h3]
    ring
  rwa [e] at this

private lemma whiten_counts_centroid {n : ℕ} (hn : 0 < n) {a b c : ℝ} (hsum : a + b + c = n) :
    (n : ℝ) / 3 + √(n : ℝ) * (scaleB 1 * (whiten 1 n a b c).2) = a ∧
    (n : ℝ) / 3 + √(n : ℝ) *
      ((scaleA 1 * (whiten 1 n a b c).1 - scaleB 1 * (whiten 1 n a b c).2) / 2) = b ∧
    (n : ℝ) / 3 + √(n : ℝ) *
      ((-(scaleA 1 * (whiten 1 n a b c).1) - scaleB 1 * (whiten 1 n a b c).2) / 2) = c := by
  obtain ⟨ha, hb, hc⟩ := whiten_counts (φ := 1) (by norm_num) hn hsum
  refine ⟨?_, ?_, ?_⟩
  · conv_rhs => rw [ha]
    ring
  · conv_rhs => rw [hb]
    ring
  · conv_rhs => rw [hc]
    ring

/-- At the centroid, the star statistic is the squared norm of the whitened frequencies. -/
theorem eventually_starS_centroid (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten 1 n a b c).1| < R →
      |(whiten 1 n a b c).2| < R →
      |starS a b c - ((whiten 1 n a b c).1 ^ 2 + (whiten 1 n a b c).2 ^ 2)| < ε := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  have hA := scaleA_pos hφ
  have hB := scaleB_pos hφ
  filter_upwards [eventually_starS_close (by positivity : 0 < (scaleA 1 + scaleB 1) * R) hε,
    eventually_gt_atTop 0] with n hn hn0 a b c hsum h₁ h₂
  obtain ⟨ea, eb, ec⟩ := whiten_counts_centroid hn0 hsum
  obtain ⟨hf, hg⟩ := abs_half_le hA hB h₁ h₂
  have hf₀ := abs_mul_le (A := scaleB 1) (B := scaleA 1) hB hA h₂
  rw [add_comm (scaleB 1)] at hf₀
  have := hn _ _ _ (by ring) hf₀ hf hg
  rw [ea, eb, ec] at this
  have hA2 := scaleA_sq hφ
  have hB2 := scaleB_sq hφ
  have e : 3 * ((scaleB 1 * (whiten 1 n a b c).2) ^ 2 +
      ((scaleA 1 * (whiten 1 n a b c).1 - scaleB 1 * (whiten 1 n a b c).2) / 2) ^ 2 +
      ((-(scaleA 1 * (whiten 1 n a b c).1) - scaleB 1 * (whiten 1 n a b c).2) / 2) ^ 2) =
      (whiten 1 n a b c).1 ^ 2 + (whiten 1 n a b c).2 ^ 2 := by
    generalize (whiten 1 n a b c).1 = x
    generalize (whiten 1 n a b c).2 = y
    have hexp : 3 * ((scaleB 1 * y) ^ 2 + ((scaleA 1 * x - scaleB 1 * y) / 2) ^ 2 +
        ((-(scaleA 1 * x) - scaleB 1 * y) / 2) ^ 2) =
        3 * (3 / 2 * (scaleB 1 ^ 2 * y ^ 2) + 1 / 2 * (scaleA 1 ^ 2 * x ^ 2)) := by
      ring
    rw [hexp, hA2, hB2]
    ring
  rwa [e] at this

/-- At the centroid, Pearson's statistic is the squared norm of the whitened frequencies. -/
theorem pearsonS_centroid {n : ℕ} (hn0 : 0 < n) {a b c : ℝ} (hsum : a + b + c = n) :
    pearsonS a b c = (whiten 1 n a b c).1 ^ 2 + (whiten 1 n a b c).2 ^ 2 := by
  have hφ : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨ea, eb, ec⟩ := whiten_counts_centroid hn0 hsum
  have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn0)).ne'
  have hsq : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have h := pearsonS_eq (s := √(n : ℝ)) (f₀ := scaleB 1 * (whiten 1 n a b c).2)
    (f₁ := (scaleA 1 * (whiten 1 n a b c).1 - scaleB 1 * (whiten 1 n a b c).2) / 2)
    (f₂ := (-(scaleA 1 * (whiten 1 n a b c).1) - scaleB 1 * (whiten 1 n a b c).2) / 2) hs (by ring)
  rw [← hsq] at h
  rw [ea, eb, ec] at h
  rw [h]
  have hA2 := scaleA_sq hφ
  have hB2 := scaleB_sq hφ
  generalize (whiten 1 n a b c).1 = x
  generalize (whiten 1 n a b c).2 = y
  have hexp : 3 * ((scaleB 1 * y) ^ 2 + ((scaleA 1 * x - scaleB 1 * y) / 2) ^ 2 +
      ((-(scaleA 1 * x) - scaleB 1 * y) / 2) ^ 2) =
      3 * (3 / 2 * (scaleB 1 ^ 2 * y ^ 2) + 1 / 2 * (scaleA 1 ^ 2 * x ^ 2)) := by
    ring
  rw [hexp, hA2, hB2]
  ring

/-- The estimate of `φ` on the line of the first topology. -/
theorem phiHat_eq (hφ : 0 < φ ∧ φ < 3 / 2) {n : ℕ} (hn : 0 < n) {a b c : ℝ} (hsum : a + b + c = n) :
    3 * (b + c) / (2 * (a + b + c)) = φ - 3 / 2 * (scaleB φ * (whiten φ n a b c).2) / √(n : ℝ) := by
  obtain ⟨ha, -, -⟩ := whiten_counts hφ hn hsum
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hbc : b + c = n - a := by linarith
  rw [hsum, hbc]
  generalize scaleB φ * (whiten φ n a b c).2 = y at ha
  rw [ha]
  field_simp
  linear_combination (-3 * y) * hsq

/-- The estimate of `φ` converges to `φ`, uniformly on bounded sets. -/
theorem eventually_phiHat_close (hφ : 0 < φ ∧ φ < 3 / 2) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).2| < R →
      |3 * (b + c) / (2 * (a + b + c)) - φ| < ε := by
  have hB := scaleB_pos hφ
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (3 / 2 * (scaleB φ * R) / ε), eventually_gt_atTop 0]
    with n hn hn0 a b c hsum h₂
  rw [phiHat_eq hφ hn0 hsum]
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  rw [div_lt_iff₀ hε] at hn
  rw [show φ - 3 / 2 * (scaleB φ * (whiten φ n a b c).2) / √(n : ℝ) - φ =
    -(3 / 2 * (scaleB φ * (whiten φ n a b c).2) / √(n : ℝ)) by ring, abs_neg, abs_div, abs_of_pos hs,
    div_lt_iff₀ hs, abs_mul, abs_mul, abs_of_pos hB]
  simp only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  have : scaleB φ * |(whiten φ n a b c).2| ≤ scaleB φ * R := by gcongr
  linarith

/-- For `φ < 1` the first topology is the most frequent, eventually. -/
theorem eventually_first_most_frequent (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ a b c : ℝ, a + b + c = n → |(whiten φ n a b c).2| < R →
      (b + c) / 2 ≤ a := by
  have hc : 0 < 1 - φ := by linarith
  have h := eventually_phiHat_close hφ (R := R) (ε := 1 - φ) hc
  filter_upwards [h, eventually_gt_atTop 0] with n hn hn0 a b c hsum h₂
  have h₁ := hn a b c hsum h₂
  have hN : 0 < a + b + c := by
    rw [hsum]
    exact_mod_cast hn0
  obtain ⟨-, h₃⟩ := abs_lt.1 h₁
  have h₄ : 3 * (b + c) / (2 * (a + b + c)) < 1 := by linarith
  rw [div_lt_one (by positivity)] at h₄
  linarith

end Phylogenetics.Trinomial
