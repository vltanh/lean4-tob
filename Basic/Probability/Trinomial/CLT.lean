module

public import Basic.Probability.Trinomial.Bridge
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.CramerWold
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Probability.Moments.Variance

/-!
# The central limit theorem for two uncorrelated functions of independent draws

For two functions `a`, `b` of a draw from a finite distribution, centred, of variance one and
uncorrelated, the normalized sums of `a` and `b` along an independent sequence converge jointly to
two independent standard normal variables: Mathlib's central limit theorem and the Cramér-Wold
device.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical RealInnerProductSpace NNReal

namespace Phylogenetics.Trinomial

variable {Γ : Type*} [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- The planar standard Gaussian law. -/
def stdPlane : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure stdPlane := by
  unfold stdPlane
  infer_instance

/-- The law of `s z₁ + t z₂` under the planar standard Gaussian law. -/
theorem hasLaw_stdPlane_add (s t : ℝ) :
    HasLaw (fun z : ℝ × ℝ ↦ s * z.1 + t * z.2) (gaussianReal 0 (s ^ 2 + t ^ 2).toNNReal) stdPlane := by
  have hindep : IndepFun (fun z : ℝ × ℝ ↦ s * z.1) (fun z : ℝ × ℝ ↦ t * z.2) stdPlane := by
    have := indepFun_prod (X := fun x : ℝ ↦ s * x) (Y := fun x : ℝ ↦ t * x)
      (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (by fun_prop) (by fun_prop)
    exact this
  have hfst : HasLaw (fun z : ℝ × ℝ ↦ s * z.1) (gaussianReal 0 (s ^ 2).toNNReal) stdPlane := by
    refine ⟨by fun_prop, ?_⟩
    have h₁ : stdPlane.map (fun z : ℝ × ℝ ↦ s * z.1) =
        ((stdPlane).map Prod.fst).map (fun x ↦ s * x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [h₁, stdPlane, Measure.map_fst_prod, measure_univ, one_smul, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.toNNReal_of_nonneg (sq_nonneg s)]
  have hsnd : HasLaw (fun z : ℝ × ℝ ↦ t * z.2) (gaussianReal 0 (t ^ 2).toNNReal) stdPlane := by
    refine ⟨by fun_prop, ?_⟩
    have h₁ : stdPlane.map (fun z : ℝ × ℝ ↦ t * z.2) =
        ((stdPlane).map Prod.snd).map (fun x ↦ t * x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [h₁, stdPlane, Measure.map_snd_prod, measure_univ, one_smul, gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.toNNReal_of_nonneg (sq_nonneg t)]
  refine ⟨by fun_prop, ?_⟩
  have := gaussianReal_add_gaussianReal_of_indepFun hindep hfst hsnd
  have h₂ : (s ^ 2).toNNReal + (t ^ 2).toNNReal = (s ^ 2 + t ^ 2).toNNReal :=
    (Real.toNNReal_add (sq_nonneg s) (sq_nonneg t)).symm
  rw [h₂] at this
  simpa [Pi.add_def] using this

variable {dist : Γ → ℝ}

theorem integral_iidSeq (hd : IsDist dist) (f : Γ → ℝ) (k : ℕ) :
    ∫ ω, f (ω k) ∂(iidSeq dist hd) = ∑ g, dist g * f g := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ ↦ hd.toPMF.toMeasure) k
  have hm : Measurable fun ω : ℕ → Γ ↦ ω k := by fun_prop
  have hf : Measurable f := Measurable.of_discrete
  rw [← integral_toPMF hd f, ← h, integral_map hm.aemeasurable hf.aestronglyMeasurable]
  rfl

theorem memLp_iidSeq (hd : IsDist dist) (f : Γ → ℝ) (k : ℕ) :
    MemLp (fun ω : ℕ → Γ ↦ f (ω k)) 2 (iidSeq dist hd) := by
  have hf : Measurable f := Measurable.of_discrete
  have hm : Measurable fun ω : ℕ → Γ ↦ f (ω k) := hf.comp (by fun_prop)
  obtain ⟨C, hC⟩ : ∃ C, ∀ g, ‖f g‖ ≤ C := by
    refine ⟨∑ g, ‖f g‖, fun g ↦ ?_⟩
    exact Finset.single_le_sum (f := fun g ↦ ‖f g‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ g)
  exact MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω ↦ hC _)

theorem identDistrib_iidSeq (hd : IsDist dist) (f : Γ → ℝ) (k : ℕ) :
    IdentDistrib (fun ω : ℕ → Γ ↦ f (ω k)) (fun ω : ℕ → Γ ↦ f (ω 0))
      (iidSeq dist hd) (iidSeq dist hd) := by
  have hf : Measurable f := Measurable.of_discrete
  have hm : ∀ j, Measurable fun ω : ℕ → Γ ↦ ω j := fun j ↦ by fun_prop
  refine ⟨(hf.comp (hm k)).aemeasurable, (hf.comp (hm 0)).aemeasurable, ?_⟩
  have h₁ : ∀ j, (iidSeq dist hd).map (fun ω : ℕ → Γ ↦ f (ω j)) =
      (hd.toPMF.toMeasure).map f := by
    intro j
    rw [← Measure.infinitePi_map_eval (fun _ : ℕ ↦ hd.toPMF.toMeasure) j,
      Measure.map_map hf (hm j)]
    rfl
  rw [h₁, h₁]

theorem iIndepFun_iidSeq (hd : IsDist dist) (f : Γ → ℝ) :
    iIndepFun (fun (k : ℕ) (ω : ℕ → Γ) ↦ f (ω k)) (iidSeq dist hd) :=
  iIndepFun_infinitePi (P := fun _ : ℕ ↦ hd.toPMF.toMeasure) (X := fun _ ↦ f)
    (fun _ ↦ Measurable.of_discrete)

/-- **The two-dimensional central limit theorem** for two uncorrelated functions of the draws. -/
theorem tendstoInDistribution_normalizedSums (hd : IsDist dist) (a b : Γ → ℝ)
    (ha₀ : ∑ g, dist g * a g = 0) (hb₀ : ∑ g, dist g * b g = 0)
    (haa : ∑ g, dist g * (a g * a g) = 1) (hbb : ∑ g, dist g * (b g * b g) = 1)
    (hab : ∑ g, dist g * (a g * b g) = 0) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → Γ) ↦
        ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, a (ω k), (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, b (ω k)))
      atTop (fun z : ℝ × ℝ ↦ z) (fun _ ↦ iidSeq dist hd) stdPlane := by
  have hma : Measurable a := Measurable.of_discrete
  have hmb : Measurable b := Measurable.of_discrete
  have hev : ∀ k, Measurable fun ω : ℕ → Γ ↦ ω k := fun k ↦ by fun_prop
  let X : ℕ → (ℕ → Γ) → EuclideanSpace ℝ (Fin 2) := fun n ω ↦
    !₂[(√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, a (ω k), (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, b (ω k)]
  let Y : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := fun z ↦ !₂[z.1, z.2]
  have hYm : Continuous Y := by
    simp only [Y]
    fun_prop
  have hXm : ∀ n, Measurable (X n) := by
    intro n
    have h₁ : Measurable fun ω : ℕ → Γ ↦ ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, a (ω k),
        (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, b (ω k)) := by
      refine Measurable.prodMk ?_ ?_
      · exact (Finset.measurable_sum _ fun k _ ↦ hma.comp (hev k)).const_mul _
      · exact (Finset.measurable_sum _ fun k _ ↦ hmb.comp (hev k)).const_mul _
    exact hYm.measurable.comp h₁
  have key : TendstoInDistribution X atTop Y (fun _ ↦ iidSeq dist hd) stdPlane := by
    refine (tendstoInDistribution_iff_tendstoInDistribution_inner hYm.measurable.aemeasurable
      (fun n ↦ (hXm n).aemeasurable)).2 fun t ↦ ?_
    let f : Γ → ℝ := fun g ↦ t 0 * a g + t 1 * b g
    have hmean : ∑ g, dist g * f g = 0 := by
      simp only [f, mul_add, Finset.sum_add_distrib]
      rw [show (∑ g, dist g * (t 0 * a g)) = t 0 * ∑ g, dist g * a g by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring,
        show (∑ g, dist g * (t 1 * b g)) = t 1 * ∑ g, dist g * b g by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, ha₀, hb₀]
      ring
    have hsq : ∑ g, dist g * (f g * f g) = (t 0) ^ 2 + (t 1) ^ 2 := by
      have : ∀ g, dist g * (f g * f g) = (t 0) ^ 2 * (dist g * (a g * a g)) +
          (2 * t 0 * t 1) * (dist g * (a g * b g)) + (t 1) ^ 2 * (dist g * (b g * b g)) := by
        intro g
        simp only [f]
        ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, haa, hbb, hab]
      ring
    have hmean' : ∫ ω, f (ω 0) ∂(iidSeq dist hd) = 0 := by rw [integral_iidSeq, hmean]
    have hvar : Var[fun ω : ℕ → Γ ↦ f (ω 0); iidSeq dist hd] = (t 0) ^ 2 + (t 1) ^ 2 := by
      rw [variance_eq_sub (memLp_iidSeq hd f 0)]
      have : ∫ ω, ((fun ω : ℕ → Γ ↦ f (ω 0)) ^ 2) ω ∂(iidSeq dist hd) =
          ∑ g, dist g * (f g * f g) := by
        rw [← integral_iidSeq hd (fun g ↦ f g * f g) 0]
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        simp [sq]
      rw [this, hsq, hmean']
      ring
    have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (X := fun (k : ℕ) (ω : ℕ → Γ) ↦ f (ω k)) (P := iidSeq dist hd) (P' := stdPlane)
      (Y := fun z : ℝ × ℝ ↦ t 0 * z.1 + t 1 * z.2)
      (by rw [hvar]; exact hasLaw_stdPlane_add _ _)
      (memLp_iidSeq hd f 0) (iIndepFun_iidSeq hd f) (fun k ↦ identDistrib_iidSeq hd f k)
    simp only [hmean', mul_zero, sub_zero] at hclt
    have hX : ∀ n ω, ⟪X n ω, t⟫ = (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, f (ω k) := by
      intro n ω
      simp only [X, f, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hY : ∀ z, ⟪Y z, t⟫ = t 0 * z.1 + t 1 * z.2 := by
      intro z
      simp only [Y, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hX, hY]
    exact hclt
  have hback := key.continuous_comp (g := fun v : EuclideanSpace ℝ (Fin 2) ↦ (v 0, v 1)) (by fun_prop)
  convert hback using 2 with n
  · ext ω <;> simp [X]
  · ext <;> simp [Y]

end Phylogenetics.Trinomial
