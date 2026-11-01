module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Independent samples from a finite distribution

The probability `iidProb dist n Ev` of an event for `n` independent draws from `dist`, as a finite
sum, with the elementary facts: bounds, union bounds, and the weak law of large numbers; and the bridge
to Mathlib's product measures, on which the central limit theorem applies.

## Main results

* `IsDist`, `iidProb`, `iidProb_nonneg`, `iidProb_le_one`, `iidProb_mono`, `iidProb_not`, `iidProb_true`,
  `iidProb_exists_le`, `iidProb_or_le`, `iidProb_sum_prod`.
* `tendsto_iidProb_forall`, `tendsto_iidProb_of_imp`, `iidProb_weak_law`: limits.
* `IsDist.toPMF`, `iidProb_eq_pi`: the bridge to product measures.
-/

@[expose] public noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical

namespace Phylogenetics

variable {Γ : Type*} [Fintype Γ]

/-- The probability that `n` independent draws from the distribution `dist` on the finite set `Γ`
lie in the event `Ev`. -/
def iidProb (dist : Γ → ℝ) (n : ℕ) (Ev : (Fin n → Γ) → Prop) : ℝ :=
  ∑ ω : Fin n → Γ, if Ev ω then ∏ i, dist (ω i) else 0

/-- `dist` is a probability distribution. -/
def IsDist (dist : Γ → ℝ) : Prop := (∀ g, 0 ≤ dist g) ∧ ∑ g, dist g = 1

variable {dist : Γ → ℝ}

theorem iidProb_nonneg (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    0 ≤ iidProb dist n Ev := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun i _ => hd.1 _
  · exact le_rfl

/-- The expectation of a product of functions of the separate draws: independence, in the finite
sum. -/
theorem iidProb_sum_prod (n : ℕ) (h : Fin n → Γ → ℝ) :
    ∑ ω : Fin n → Γ, (∏ i, dist (ω i)) * ∏ i, h i (ω i) = ∏ i, ∑ g, dist g * h i g := by
  have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Γ)) (fun i g => dist g * h i g)
  rw [Fintype.piFinset_univ] at this
  rw [this]
  exact Finset.sum_congr rfl fun ω _ => (Finset.prod_mul_distrib).symm

theorem iidProb_true (hd : IsDist dist) (n : ℕ) : iidProb dist n (fun _ => True) = 1 := by
  have := iidProb_sum_prod (dist := dist) n (fun _ _ => 1)
  simpa [iidProb, hd.2] using this

theorem iidProb_mono (hd : IsDist dist) {n : ℕ} {Ev Ev' : (Fin n → Γ) → Prop}
    (h : ∀ ω, Ev ω → Ev' ω) : iidProb dist n Ev ≤ iidProb dist n Ev' := by
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw : 0 ≤ ∏ i, dist (ω i) := Finset.prod_nonneg fun i _ => hd.1 _
  by_cases h1 : Ev ω
  · simp [h1, h ω h1]
  · simp only [h1, ite_false]
    split_ifs
    · exact hw
    · exact le_rfl

theorem iidProb_le_one (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    iidProb dist n Ev ≤ 1 := by
  rw [← iidProb_true hd n]
  exact iidProb_mono hd fun _ _ => trivial

theorem iidProb_not (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    iidProb dist n (fun ω => ¬ Ev ω) = 1 - iidProb dist n Ev := by
  rw [← iidProb_true hd n, eq_sub_iff_add_eq]
  unfold iidProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : Ev ω <;> simp [h]

/-- The union bound. -/
theorem iidProb_exists_le (hd : IsDist dist) {ι : Type*} [Fintype ι] {n : ℕ}
    (Ev : ι → (Fin n → Γ) → Prop) :
    iidProb dist n (fun ω => ∃ i, Ev i ω) ≤ ∑ i, iidProb dist n (Ev i) := by
  unfold iidProb
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw : 0 ≤ ∏ i, dist (ω i) := Finset.prod_nonneg fun i _ => hd.1 _
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    calc ∏ i, dist (ω i) = if Ev i ω then ∏ i, dist (ω i) else 0 := by simp [hi]
      _ ≤ _ := Finset.single_le_sum (f := fun i => if Ev i ω then ∏ i, dist (ω i) else 0)
            (fun j _ => by split_ifs <;> simp [hw]) (Finset.mem_univ i)
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hw]

/-- The union bound for two events. -/
theorem iidProb_or_le (hd : IsDist dist) {n : ℕ} (Ev Ev' : (Fin n → Γ) → Prop) :
    iidProb dist n (fun ω => Ev ω ∨ Ev' ω) ≤ iidProb dist n Ev + iidProb dist n Ev' := by
  rw [iidProb, iidProb, iidProb, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw : 0 ≤ ∏ i, dist (ω i) := Finset.prod_nonneg fun i _ => hd.1 _
  by_cases h1 : Ev ω <;> by_cases h2 : Ev' ω <;> simp [h1, h2, hw]

/-- If each of finitely many events has probability tending to one, so does their intersection. -/
theorem tendsto_iidProb_forall (hd : IsDist dist) {ι : Type*} [Fintype ι]
    (Ev : ι → (n : ℕ) → (Fin n → Γ) → Prop)
    (h : ∀ i, Tendsto (fun n => iidProb dist n (Ev i n)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω => ∀ i, Ev i n ω) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n => 1 - ∑ i, (1 - iidProb dist n (Ev i n))) atTop (𝓝 1) := by
    have : Tendsto (fun n => ∑ i, (1 - iidProb dist n (Ev i n))) atTop (𝓝 (∑ _i : ι, (1 - 1 : ℝ))) :=
      tendsto_finsetSum _ fun i _ => tendsto_const_nhds.sub (h i)
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => iidProb_le_one hd n _)
  have h1 := iidProb_exists_le hd (fun i ω => ¬ Ev i n ω)
  simp only [iidProb_not hd] at h1
  have h2 : iidProb dist n (fun ω => ∃ i, ¬ Ev i n ω) = 1 - iidProb dist n fun ω => ∀ i, Ev i n ω := by
    rw [← iidProb_not hd]
    simp only [not_forall]
  rw [h2] at h1
  dsimp only
  linarith

/-- An event containing, for large `n`, an event with probability tending to one. -/
theorem tendsto_iidProb_of_imp (hd : IsDist dist) {Ev Ev' : (n : ℕ) → (Fin n → Γ) → Prop}
    (himp : ∀ᶠ n in atTop, ∀ ω, Ev n ω → Ev' n ω)
    (h : Tendsto (fun n => iidProb dist n (Ev n)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n (Ev' n)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds ?_
    (Eventually.of_forall fun n => iidProb_le_one hd n _)
  filter_upwards [himp] with n hn using iidProb_mono hd hn

/-- If two events have probability tending to one, so does their intersection. -/
theorem tendsto_iidProb_and (hd : IsDist dist)
    {P Q : (n : ℕ) → (Fin n → Γ) → Prop}
    (hP : Tendsto (fun n => iidProb dist n (P n)) atTop (𝓝 1))
    (hQ : Tendsto (fun n => iidProb dist n (Q n)) atTop (𝓝 1)) :
    Tendsto (fun n => iidProb dist n fun ω => P n ω ∧ Q n ω) atTop (𝓝 1) := by
  have h := tendsto_iidProb_forall hd (ι := Bool) (fun b n ω => if b = true then P n ω else Q n ω)
    (by intro b; cases b <;> simpa)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_) h
  exact ⟨by simpa using hω true, by simpa using hω false⟩

/-! ### The second moment of a sum -/

/-- The expectation of `Y (ω i) * Y (ω j)` for `i ≠ j`, when `Y` is centred. -/
private theorem sum_mul_of_ne {n : ℕ} {Y : Γ → ℝ} (hY : ∑ g, dist g * Y g = 0)
    {i j : Fin n} (hij : i ≠ j) :
    ∑ ω : Fin n → Γ, (∏ k, dist (ω k)) * (Y (ω i) * Y (ω j)) = 0 := by
  have key := iidProb_sum_prod (dist := dist) n
    (fun k g => (if k = i then Y g else 1) * (if k = j then Y g else 1))
  have hprod : ∀ ω : Fin n → Γ,
      ∏ k, ((if k = i then Y (ω k) else 1) * (if k = j then Y (ω k) else 1)) =
        Y (ω i) * Y (ω j) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' , Finset.prod_ite_eq']
    simp
  simp only [hprod] at key
  rw [key]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simpa [hij] using hY

/-- The expectation of `Y (ω i) ^ 2`. -/
private theorem sum_mul_self (hd : IsDist dist) {n : ℕ} (Y : Γ → ℝ) (i : Fin n) :
    ∑ ω : Fin n → Γ, (∏ k, dist (ω k)) * (Y (ω i) * Y (ω i)) = ∑ g, dist g * (Y g * Y g) := by
  have key := iidProb_sum_prod (dist := dist) n (fun k g => if k = i then Y g * Y g else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true] at key
  rw [key, Finset.prod_eq_single i]
  · simp
  · intro k _ hk
    simp [hk, hd.2]
  · simp

/-- The second moment of a sum of `n` independent centred terms. -/
private theorem sum_sq (hd : IsDist dist) (n : ℕ) {Y : Γ → ℝ} (hY : ∑ g, dist g * Y g = 0) :
    ∑ ω : Fin n → Γ, (∏ k, dist (ω k)) * (∑ i, Y (ω i)) ^ 2 =
      n * ∑ g, dist g * (Y g * Y g) := by
  have h1 : ∀ ω : Fin n → Γ, (∏ k, dist (ω k)) * (∑ i, Y (ω i)) ^ 2 =
      ∑ i, ∑ j, (∏ k, dist (ω k)) * (Y (ω i) * Y (ω j)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ i : Fin n, ∑ ω : Fin n → Γ, ∑ j, (∏ k, dist (ω k)) * (Y (ω i) * Y (ω j)) =
      ∑ g, dist g * (Y g * Y g) := by
    intro i
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · exact sum_mul_self hd Y i
    · intro j _ hj
      exact sum_mul_of_ne hY hj.symm
    · simp
  simp [h2]

/-- **Chebyshev's inequality** for the mean of `n` independent draws. -/
private theorem iidProb_chebyshev (hd : IsDist dist) (f : Γ → ℝ) {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : 0 < n) :
    1 - (∑ g, dist g * ((f g - ∑ g, dist g * f g) * (f g - ∑ g, dist g * f g))) / (n * ε ^ 2) ≤
      iidProb dist n fun ω => |(∑ i, f (ω i)) / n - ∑ g, dist g * f g| < ε := by
  set μ := ∑ g, dist g * f g with hμ
  set Y : Γ → ℝ := fun g => f g - μ with hYdef
  have hY : ∑ g, dist g * Y g = 0 := by
    simp only [hYdef, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd.2, one_mul, ← hμ, sub_self]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < (n * ε) ^ 2 := by positivity
  have hmean : ∀ ω : Fin n → Γ, (∑ i, f (ω i)) / n - μ = (∑ i, Y (ω i)) / n := by
    intro ω
    simp only [hYdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hbad : iidProb dist n (fun ω => ¬ |(∑ i, f (ω i)) / n - μ| < ε) ≤
      (n * ∑ g, dist g * (Y g * Y g)) / (n * ε) ^ 2 := by
    rw [← sum_sq hd n hY, Finset.sum_div]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hw : 0 ≤ ∏ i, dist (ω i) := Finset.prod_nonneg fun i _ => hd.1 _
    split_ifs with h
    · dsimp only at h
      rw [not_lt, hmean, abs_div, abs_of_pos hn', le_div_iff₀ hn'] at h
      have h' : (n * ε) ^ 2 ≤ (∑ i, Y (ω i)) ^ 2 := by
        rw [← sq_abs (∑ i, Y (ω i))]
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      rw [le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left h' hw
    · positivity
  have hnot := iidProb_not hd n fun ω => |(∑ i, f (ω i)) / n - μ| < ε
  have heq : (n * ∑ g, dist g * (Y g * Y g)) / (n * ε) ^ 2 =
      (∑ g, dist g * (Y g * Y g)) / (n * ε ^ 2) := by
    field_simp
  rw [heq] at hbad
  rw [hnot] at hbad
  linarith

/-- **The weak law of large numbers** for a function of `n` independent draws. -/
theorem iidProb_weak_law (hd : IsDist dist) (f : Γ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => iidProb dist n fun ω =>
      |(∑ i, f (ω i)) / n - ∑ g, dist g * f g| < ε) atTop (𝓝 1) := by
  set C := ∑ g, dist g * ((f g - ∑ g, dist g * f g) * (f g - ∑ g, dist g * f g)) with hC
  have hlow : Tendsto (fun n : ℕ => 1 - C / (n * ε ^ 2)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => C / (n * ε ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) * ε ^ 2) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
      exact h1.const_div_atTop C
    simpa using tendsto_const_nhds.sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => iidProb_le_one hd n _)
  filter_upwards [eventually_gt_atTop 0] with n hn using iidProb_chebyshev hd f hε hn

/-! ### The bridge to product measures -/

/-- The distribution `dist`, as a `PMF`. -/
def IsDist.toPMF (hd : IsDist dist) : PMF Γ :=
  PMF.ofFintype (fun g => ENNReal.ofReal (dist g)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun g _ => hd.1 g, hd.2, ENNReal.ofReal_one])

theorem IsDist.toPMF_apply (hd : IsDist dist) (g : Γ) : hd.toPMF g = ENNReal.ofReal (dist g) := rfl

/-- `iidProb dist n Ev` is the probability of `Ev` under the `n`-fold product of the law of `dist`,
for any σ-algebra on `Γ` with measurable singletons (on a finite type, the discrete one). -/
theorem iidProb_eq_pi [MeasurableSpace Γ] [MeasurableSingletonClass Γ] (hd : IsDist dist) (n : ℕ)
    (Ev : (Fin n → Γ) → Prop) :
    iidProb dist n Ev = (Measure.pi fun _ : Fin n => hd.toPMF.toMeasure).real {ω | Ev ω} := by
  have hsing : ∀ g : Γ, (hd.toPMF.toMeasure).real {g} = dist g := by
    intro g
    rw [measureReal_def, hd.toPMF.toMeasure_apply_singleton g (measurableSet_singleton g),
      hd.toPMF_apply, ENNReal.toReal_ofReal (hd.1 g)]
  have hset : {ω | Ev ω} = ((univ.filter Ev : Finset (Fin n → Γ)) : Set (Fin n → Γ)) := by
    ext ω; simp
  rw [hset, ← sum_measureReal_singleton, iidProb, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs
  · rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i _ => (hsing (ω i)).symm
  · rfl

end Phylogenetics
