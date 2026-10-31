module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Transferring convergence in distribution to statistics

A sequence `W n` of random vectors in the plane converges in distribution to `ν`, and statistics
`S n` are close to a continuous function `T` of `W n` uniformly on the events `‖W n‖ < R`. Then
`S n` converges in distribution to `T` under `ν` (the extended continuous mapping theorem, in the form
that the statistics of a sample need), and events containing `W n ∈ U` for an open `U` have
probability at least `ν U` in the limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Phylogenetics.Trinomial

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)] {W : ∀ n, Ω n → ℝ × ℝ} {ν : Measure (ℝ × ℝ)}
  [IsProbabilityMeasure ν]

/-- Portmanteau, in the form used below. -/
theorem eventually_lt_measure_preimage_of_isOpen
    (h : TendstoInDistribution W atTop (fun z : ℝ × ℝ ↦ z) μ ν) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {c : ℝ≥0∞} (hc : c < ν U) : ∀ᶠ n in atTop, c < μ n (W n ⁻¹' U) := by
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hU
  simp only [ProbabilityMeasure.coe_mk] at hp
  have hν : ν.map (fun z : ℝ × ℝ ↦ z) = ν := Measure.map_id'
  rw [hν] at hp
  have := eventually_lt_of_lt_liminf (hc.trans_le hp) (by isBoundedDefault)
  filter_upwards [this] with n hn
  rwa [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hU.measurableSet] at hn

/-- An event containing `W n ∈ U` for large `n`, with `U` open: lower bound of its probability. -/
theorem eventually_lt_measure_of_isOpen
    (h : TendstoInDistribution W atTop (fun z : ℝ × ℝ ↦ z) μ ν) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {A : ∀ n, Set (Ω n)} (hA : ∀ᶠ n in atTop, ∀ ω, W n ω ∈ U → ω ∈ A n)
    {c : ℝ≥0∞} (hc : c < ν U) : ∀ᶠ n in atTop, c < μ n (A n) := by
  filter_upwards [eventually_lt_measure_preimage_of_isOpen h hU hc, hA] with n hn hAn
  exact hn.trans_le (measure_mono hAn)

/-- The closed set of the plane on which both coordinates are bounded by `R` is large. -/
theorem exists_lt_measure_box (ν : Measure (ℝ × ℝ)) {U : Set (ℝ × ℝ)} {c : ℝ≥0∞} (hc : c < ν U) :
    ∃ R : ℝ, 0 < R ∧ c < ν (U ∩ Metric.ball 0 R) := by
  have hmono : Monotone fun k : ℕ ↦ U ∩ Metric.ball (0 : ℝ × ℝ) (k + 1) := by
    intro j k hjk
    refine Set.inter_subset_inter_right _ (Metric.ball_subset_ball ?_)
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  have hunion : ⋃ k : ℕ, U ∩ Metric.ball (0 : ℝ × ℝ) (k + 1) = U := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_and_left, and_iff_left_iff_imp]
    intro _
    obtain ⟨k, hk⟩ := exists_nat_gt (dist z 0)
    exact ⟨k, Metric.mem_ball.2 (hk.trans (by linarith))⟩
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hunion] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (lt_mem_nhds hc)).exists
  exact ⟨k + 1, by positivity, hk⟩

variable {S : ∀ n, Ω n → ℝ} {T : ℝ × ℝ → ℝ}

/-- `S n` is close to `T (W n)`, uniformly on the event that `W n` is bounded. -/
def CloseOnBalls (W : ∀ n, Ω n → ℝ × ℝ) (S : ∀ n, Ω n → ℝ) (T : ℝ × ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ ω : Ω n, |(W n ω).1| < R → |(W n ω).2| < R →
    |S n ω - T (W n ω)| < ε

theorem mem_ball_iff {z : ℝ × ℝ} {R : ℝ} : z ∈ Metric.ball (0 : ℝ × ℝ) R ↔ |z.1| < R ∧ |z.2| < R := by
  rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs, Real.norm_eq_abs]

/-- **The extended continuous mapping theorem.** -/
theorem tendstoInDistribution_of_closeOnBalls
    (h : TendstoInDistribution W atTop (fun z : ℝ × ℝ ↦ z) μ ν)
    (hS : ∀ n, AEMeasurable (S n) (μ n)) (hT : Continuous T) (hclose : CloseOnBalls W S T) :
    TendstoInDistribution S atTop T μ ν := by
  refine ⟨hS, hT.aemeasurable, ?_⟩
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G hG ↦ ?_
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply hT.measurable hG.measurableSet]
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  -- thin the open set `G`
  let V : ℕ → Set ℝ := fun k ↦ (Metric.cthickening ((k : ℝ) + 1)⁻¹ Gᶜ)ᶜ
  have hVopen : ∀ k, IsOpen (V k) := fun k ↦ (Metric.isClosed_cthickening).isOpen_compl
  have hVmono : Monotone V := by
    intro j k hjk
    refine Set.compl_subset_compl.2 (Metric.cthickening_mono ?_ _)
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    exact inv_anti₀ (by positivity) (by linarith)
  have hVunion : ⋃ k, V k = G := by
    have hcl : IsClosed Gᶜ := hG.isClosed_compl
    have : ⋂ k : ℕ, Metric.cthickening ((k : ℝ) + 1)⁻¹ Gᶜ = Gᶜ := by
      refine Set.Subset.antisymm ?_ ?_
      · have hsub : ⋂ k : ℕ, Metric.cthickening ((k : ℝ) + 1)⁻¹ Gᶜ ⊆ closure Gᶜ := by
          rw [Metric.closure_eq_iInter_cthickening]
          refine Set.subset_iInter₂ fun δ hδ ↦ ?_
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
          refine (Set.iInter_subset _ k).trans (Metric.cthickening_mono ?_ _)
          rw [one_div] at hk
          exact hk.le
        rwa [hcl.closure_eq] at hsub
      · exact Set.subset_iInter fun k ↦ Metric.self_subset_cthickening _
    simp only [V]
    rw [← Set.compl_iInter, this, compl_compl]
  have hTmono : Monotone fun k ↦ T ⁻¹' V k := fun _ _ hjk ↦ Set.preimage_mono (hVmono hjk)
  have hTunion : ⋃ k, T ⁻¹' V k = T ⁻¹' G := by rw [← Set.preimage_iUnion, hVunion]
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hTmono
  rw [hTunion] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (lt_mem_nhds hc)).exists
  have hTopen : IsOpen (T ⁻¹' V k) := (hVopen k).preimage hT
  obtain ⟨R, hR, hRc⟩ := exists_lt_measure_box ν hk
  have hUopen : IsOpen (T ⁻¹' V k ∩ Metric.ball 0 R) := hTopen.inter Metric.isOpen_ball
  have hA : ∀ᶠ n in atTop, ∀ ω, W n ω ∈ T ⁻¹' V k ∩ Metric.ball 0 R → ω ∈ S n ⁻¹' G := by
    have hε : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
    filter_upwards [hclose R hR _ hε] with n hn ω hω
    obtain ⟨hω₁, hω₂⟩ := hω
    obtain ⟨hb₁, hb₂⟩ := mem_ball_iff.1 hω₂
    have hclose' := hn ω hb₁ hb₂
    by_contra hcon
    refine hω₁ ?_
    have hmem : S n ω ∈ Gᶜ := hcon
    refine Metric.mem_cthickening_of_dist_le _ (S n ω) _ _ hmem ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact hclose'.le
  have := eventually_lt_measure_of_isOpen h hUopen hA hRc
  refine le_liminf_of_le (by isBoundedDefault) (this.mono fun n hn ↦ ?_)
  rw [Measure.map_apply_of_aemeasurable (hS n) hG.measurableSet]
  exact hn.le

end Phylogenetics.Trinomial
