module

public import Basic.Probability.IID
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Independent draws from a finite distribution, as product measures

`iidProb dist n Ev` (a finite sum, `Basic/Phylogenetics/Defs.lean`) is the probability of `Ev` under
the first `n` coordinates of the independent sequence with marginal `dist` (`iidProb_eq_iidSeq`). It
is also compatible with relabelling the draws (`iidProb_comp_label`).
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace Phylogenetics.Trinomial

variable {Γ : Type*} [Fintype Γ]

section Measure

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- The law of the independent sequence of draws from `dist`. -/
def iidSeq (dist : Γ → ℝ) (hd : IsDist dist) : Measure (ℕ → Γ) :=
  Measure.infinitePi fun _ : ℕ ↦ hd.toPMF.toMeasure

instance (dist : Γ → ℝ) (hd : IsDist dist) : IsProbabilityMeasure (iidSeq dist hd) := by
  unfold iidSeq
  infer_instance

theorem toPMF_singleton {dist : Γ → ℝ} (hd : IsDist dist) (g : Γ) :
    hd.toPMF.toMeasure {g} = ENNReal.ofReal (dist g) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton g)]
  rfl

/-- The expectation of a function of one draw. -/
theorem integral_toPMF {dist : Γ → ℝ} (hd : IsDist dist) (f : Γ → ℝ) :
    ∫ g, f g ∂hd.toPMF.toMeasure = ∑ g, dist g * f g := by
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp [hd.toPMF_apply, ENNReal.toReal_ofReal (hd.1 g)]

/-- The cylinder of a finite sample. -/
theorem iidSeq_real_cylinder {dist : Γ → ℝ} (hd : IsDist dist) {n : ℕ} (η : Fin n → Γ) :
    (iidSeq dist hd).real {ω : ℕ → Γ | (fun i : Fin n ↦ ω i) = η} = ∏ i, dist (η i) := by
  have hset : {ω : ℕ → Γ | (fun i : Fin n ↦ ω i) = η} =
      Set.pi (Finset.range n : Finset ℕ) (fun k ↦ if h : k < n then {η ⟨k, h⟩} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio, funext_iff]
    constructor
    · intro h k hk
      simp only [hk, dite_eq_left, Set.mem_singleton_iff]
      exact h ⟨k, hk⟩
    · intro h i
      have := h i i.2
      simpa [i.2] using this
  rw [hset, measureReal_def, iidSeq, Measure.infinitePi_pi]
  · rw [Finset.prod_range, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp only [i.2, dite_eq_left, Fin.eta, toPMF_singleton, ENNReal.toReal_ofReal (hd.1 _)]
  · intro k _
    split_ifs
    · exact measurableSet_singleton _
    · exact MeasurableSet.univ

/-- `iidProb` is the probability of the event under the first `n` coordinates of the independent
sequence. -/
theorem iidProb_eq_iidSeq {dist : Γ → ℝ} (hd : IsDist dist) (n : ℕ) (Ev : (Fin n → Γ) → Prop) :
    iidProb dist n Ev = (iidSeq dist hd).real {ω : ℕ → Γ | Ev fun i : Fin n ↦ ω i} := by
  have hset : {ω : ℕ → Γ | Ev fun i : Fin n ↦ ω i} =
      ⋃ η ∈ (Finset.univ.filter Ev : Finset (Fin n → Γ)),
        {ω : ℕ → Γ | (fun i : Fin n ↦ ω i) = η} := by
    ext ω
    simp
  have hmeas : ∀ η : Fin n → Γ, MeasurableSet {ω : ℕ → Γ | (fun i : Fin n ↦ ω i) = η} := by
    intro η
    have : Measurable fun ω : ℕ → Γ ↦ fun i : Fin n ↦ ω i := by fun_prop
    exact this (measurableSet_singleton η)
  rw [hset, measureReal_biUnion_finset _ (fun η _ ↦ hmeas η)]
  · simp only [iidSeq_real_cylinder hd]
    rw [iidProb, Finset.sum_filter]
  · intro η _ η' _ hne
    refine Set.disjoint_left.2 fun ω h h' ↦ hne ?_
    have h₁ : (fun i : Fin n ↦ ω i) = η := h
    have h₂ : (fun i : Fin n ↦ ω i) = η' := h'
    exact h₁.symm.trans h₂

end Measure

variable {T : Type*} [Fintype T]

/-- The distribution of `label g` for a draw `g` from `dist`. -/
def pushDist (dist : Γ → ℝ) (label : Γ → T) (t : T) : ℝ :=
  ∑ g, if label g = t then dist g else 0

theorem pushDist_isDist {dist : Γ → ℝ} (hd : IsDist dist) (label : Γ → T) :
    IsDist (pushDist dist label) := by
  refine ⟨fun t ↦ Finset.sum_nonneg fun g _ ↦ ?_, ?_⟩
  · split_ifs
    · exact hd.1 g
    · exact le_rfl
  · rw [← hd.2]
    simp only [pushDist]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp

/-- Relabelling the draws. -/
theorem iidProb_comp_label {dist : Γ → ℝ} (label : Γ → T) (n : ℕ) (Ev : (Fin n → T) → Prop) :
    iidProb dist n (fun ω ↦ Ev fun i ↦ label (ω i)) = iidProb (pushDist dist label) n Ev := by
  have hfib : ∀ η : Fin n → T, ∏ i, pushDist dist label (η i) =
      ∑ ω : Fin n → Γ, if (fun i ↦ label (ω i)) = η then ∏ i, dist (ω i) else 0 := by
    intro η
    simp only [pushDist]
    rw [Finset.prod_univ_sum (fun _ ↦ Finset.univ) (fun i g ↦ if label g = η i then dist g else 0),
      Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    by_cases h : (fun i ↦ label (ω i)) = η
    · rw [ite_eq_left h]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [ite_eq_left (congrFun h i)]
    · rw [ite_eq_right h]
      have : ∃ i, label (ω i) ≠ η i := by
        by_contra hcon
        push Not at hcon
        exact h (funext hcon)
      obtain ⟨i, hi⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  simp only [iidProb, hfib]
  have : ∀ η : Fin n → T, (if Ev η then ∑ ω : Fin n → Γ,
        (if (fun i ↦ label (ω i)) = η then ∏ i, dist (ω i) else 0) else 0) =
      ∑ ω : Fin n → Γ, if Ev η then
        (if (fun i ↦ label (ω i)) = η then ∏ i, dist (ω i) else 0) else 0 := by
    intro η
    split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Finset.sum_eq_single (fun i ↦ label (ω i))]
  · simp
  · intro η _ hne
    simp [hne.symm]
  · simp

end Phylogenetics.Trinomial
