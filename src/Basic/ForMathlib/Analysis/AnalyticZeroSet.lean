module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The zero set of a real analytic function is null

A real analytic function on a finite product of copies of `ℝ` that is not identically zero vanishes
only on a set of measure zero. This module proves it for Lebesgue measure and, more generally, for a
product of measures on `ℝ` of which some may have an atom at `0`.

With atoms at `0` on a set `A` of coordinates, the theorems assume that the function is nonzero
somewhere on the face `{x | ∀ i ∈ A, x i = 0}`. This face lies in every face
`{x | ∀ i ∈ S, x i = 0}` with `S ⊆ A`, so the function is then nonzero on each of those too. The
assumption cannot be dropped: when the atoms have positive mass and the other factors are nonzero,
the face has positive measure.

## Main results

* `AnalyticOnNhd.countable_setOf_eq_zero`: in one variable the zero set is countable.
* `AnalyticOnNhd.measure_pi_setOf_eq_zero`: a product measure, with atoms at `0` on a set of
  coordinates, on `ι → ℝ`.
* `AnalyticOnNhd.measure_prod_pi_setOf_eq_zero`: the same on `(ι → ℝ) × (κ → ℝ)`.
* `AnalyticOnNhd.volume_setOf_eq_zero`, `AnalyticOnNhd.prod_pi_volume_setOf_eq_zero`: Lebesgue
  measure.
* `AnalyticOnNhd.prod_pi_dirac_add_restrict_setOf_eq_zero`: `δ₀ + Lebesgue` or restricted Lebesgue
  measure on each coordinate.

## Proof

By induction on the number of coordinates. Given a point `(t₀, y₀)` where `f` is nonzero, the
function `y ↦ f (t₀, y)` is analytic and nonzero at `y₀`, so by induction `f (t₀, y) ≠ 0` for almost
every `y`. For such `y` the function `t ↦ f (t, y)` is analytic and nonzero at `t₀`, so it has
countably many zeros; if the first coordinate has an atom at `0`, then `t₀ = 0`, so the atom is not
one of them. Fubini's theorem concludes.
-/

@[expose] public section

open MeasureTheory Set

namespace AnalyticOnNhd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real analytic function of one variable that is not identically zero has countably many
zeros. -/
theorem countable_setOf_eq_zero {g : ℝ → E} (hg : AnalyticOnNhd ℝ g univ) {t₀ : ℝ}
    (ht₀ : g t₀ ≠ 0) : {t | g t = 0}.Countable := by
  have h : IsDiscrete (g ⁻¹' {0}ᶜ)ᶜ := (mem_codiscrete'.1 (hg.preimage_zero_mem_codiscrete ht₀)).2
  have hs : (g ⁻¹' {0}ᶜ)ᶜ = {t | g t = 0} := by ext; simp
  rw [hs] at h
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete h

/-- The zero set of a nonzero real analytic function of one variable is null for a measure
absolutely continuous with respect to Lebesgue measure. -/
theorem measure_setOf_eq_zero_of_absolutelyContinuous {μ : Measure ℝ} (hμ : μ ≪ volume)
    {g : ℝ → E} (hg : AnalyticOnNhd ℝ g univ) {t₀ : ℝ} (ht₀ : g t₀ ≠ 0) :
    μ {t | g t = 0} = 0 :=
  hμ ((hg.countable_setOf_eq_zero ht₀).measure_zero volume)

/-- The zero set of a real analytic function of one variable that is nonzero at `0` is null for a
measure absolutely continuous with respect to `δ₀ + Lebesgue`. -/
theorem measure_setOf_eq_zero_of_absolutelyContinuous_dirac_add {μ : Measure ℝ}
    (hμ : μ ≪ Measure.dirac 0 + volume) {g : ℝ → E} (hg : AnalyticOnNhd ℝ g univ)
    (h₀ : g 0 ≠ 0) : μ {t | g t = 0} = 0 := by
  refine hμ ?_
  rw [Measure.add_apply, (hg.countable_setOf_eq_zero h₀).measure_zero volume, add_zero,
    Measure.dirac_apply, indicator_of_notMem (by simpa using h₀)]

/-- A set in a product is null if almost all of its slices in the second coordinate are null. -/
private lemma measure_prod_eq_zero_of_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {s : Set (X × Y)}
    (hs : MeasurableSet s) (h : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' s) = 0) :
    μ.prod ν s = 0 := by
  rw [Measure.prod_apply_symm hs]
  exact (lintegral_congr_ae h).trans lintegral_zero

/-- Inserting a coordinate is an analytic map. -/
private lemma analyticOnNhd_insertNth {n : ℕ} (i : Fin (n + 1)) :
    AnalyticOnNhd ℝ (fun p : ℝ × (Fin n → ℝ) => (i.insertNth p.1 p.2 : Fin (n + 1) → ℝ)) univ := by
  intro p _
  rw [analyticAt_pi_iff, i.forall_iff_succAbove]
  refine ⟨by simpa using analyticAt_fst, fun j => ?_⟩
  simp only [Fin.insertNth_apply_succAbove]
  exact (analyticAt_pi_iff.1 analyticAt_snd) j

/-- `AnalyticOnNhd.measure_pi_setOf_eq_zero` for `Fin n`. -/
private theorem measure_pi_fin_setOf_eq_zero {n : ℕ} {μ : Fin n → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] {A : Set (Fin n)}
    (hA : ∀ i ∈ A, μ i ≪ Measure.dirac 0 + volume) (hAc : ∀ i ∉ A, μ i ≪ volume)
    {f : (Fin n → ℝ) → E} (hf : AnalyticOnNhd ℝ f univ) {x : Fin n → ℝ}
    (hxA : ∀ i ∈ A, x i = 0) (hx : f x ≠ 0) : Measure.pi μ {y | f y = 0} = 0 := by
  induction n with
  | zero =>
    have h : {y | f y = 0} = ∅ := by
      ext y
      simpa [Subsingleton.elim y x] using hx
    simp [h]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he := (measurePreserving_piFinSuccAbove μ 0).symm e
    let F : ℝ × (Fin n → ℝ) → E := fun p => f (e.symm p)
    have hF : AnalyticOnNhd ℝ F univ := hf.comp (analyticOnNhd_insertNth 0) (mapsTo_univ _ _)
    have hF₁ (y : Fin n → ℝ) : AnalyticOnNhd ℝ (fun t => F (t, y)) univ :=
      fun t _ => (hF (t, y) (mem_univ _)).curry_left
    have hF₂ (t : ℝ) : AnalyticOnNhd ℝ (fun y => F (t, y)) univ :=
      fun y _ => (hF (t, y) (mem_univ _)).curry_right
    have hZ : MeasurableSet {p | F p = 0} :=
      (isClosed_eq (continuousOn_univ.1 hF.continuousOn) continuous_const).measurableSet
    have hx' : F (x 0, Fin.removeNth 0 x) = f x := congrArg f (Fin.insertNth_self_removeNth 0 x)
    have hae : Measure.pi (fun j => μ (Fin.succAbove 0 j)) {y | F (x 0, y) = 0} = 0 :=
      ih (A := {j | Fin.succAbove 0 j ∈ A}) (fun j hj => hA _ hj) (fun j hj => hAc _ hj) (hF₂ _)
        (x := Fin.removeNth 0 x) (fun j hj => hxA _ hj) (by rwa [hx'])
    rw [← he.measure_preimage_equiv]
    refine measure_prod_eq_zero_of_ae hZ ?_
    filter_upwards [ae_iff.2 (by simpa using hae : Measure.pi (fun j => μ (Fin.succAbove 0 j))
      {y | ¬ F (x 0, y) ≠ 0} = 0)] with y hy
    by_cases h₀ : (0 : Fin (n + 1)) ∈ A
    · rw [hxA 0 h₀] at hy
      exact measure_setOf_eq_zero_of_absolutelyContinuous_dirac_add (hA 0 h₀) (hF₁ y) hy
    · exact measure_setOf_eq_zero_of_absolutelyContinuous (hAc 0 h₀) (hF₁ y) hy

/-- **The zero set of a real analytic function is null**, for a product of σ-finite measures on `ℝ`
that are absolutely continuous with respect to Lebesgue measure, except on a set `A` of coordinates
where they may also have an atom at `0`, assuming that the function is nonzero somewhere on the face
where the coordinates of `A` vanish. -/
theorem measure_pi_setOf_eq_zero {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, SigmaFinite (μ i)] {A : Set ι}
    (hA : ∀ i ∈ A, μ i ≪ Measure.dirac 0 + volume) (hAc : ∀ i ∉ A, μ i ≪ volume)
    {f : (ι → ℝ) → E} (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, (∀ i ∈ A, x i = 0) ∧ f x ≠ 0) :
    Measure.pi μ {y | f y = 0} = 0 := by
  obtain ⟨x, hxA, hx⟩ := h
  let e := (Fintype.equivFin ι).symm
  let c := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hc : AnalyticOnNhd ℝ c univ := by
    intro y _
    rw [analyticAt_pi_iff, e.surjective.forall]
    intro j
    simp only [c, MeasurableEquiv.piCongrLeft_apply_apply]
    exact (analyticAt_pi_iff.1 analyticAt_id) j
  rw [← (measurePreserving_piCongrLeft (α := fun _ : ι => ℝ) μ e).measure_preimage_equiv]
  refine measure_pi_fin_setOf_eq_zero (A := e ⁻¹' A) (fun j hj => hA _ hj) (fun j hj => hAc _ hj)
    (f := fun y => f (c y)) (hf.comp hc (mapsTo_univ _ _)) (x := c.symm x) ?_ (by simpa using hx)
  intro j hj
  exact hxA _ hj

/-- **The zero set of a real analytic function is null**, on a product of two finite products of
`ℝ`, for the measures of `AnalyticOnNhd.measure_pi_setOf_eq_zero` on the first factor and measures
absolutely continuous with respect to Lebesgue measure on the second. -/
theorem measure_prod_pi_setOf_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ] {μ : ι → Measure ℝ}
    {ν : κ → Measure ℝ} [∀ i, SigmaFinite (μ i)] [∀ j, SigmaFinite (ν j)] {A : Set ι}
    (hA : ∀ i ∈ A, μ i ≪ Measure.dirac 0 + volume) (hAc : ∀ i ∉ A, μ i ≪ volume)
    (hν : ∀ j, ν j ≪ volume) {f : (ι → ℝ) × (κ → ℝ) → E} (hf : AnalyticOnNhd ℝ f univ)
    (h : ∃ x : (ι → ℝ) × (κ → ℝ), (∀ i ∈ A, x.1 i = 0) ∧ f x ≠ 0) :
    ((Measure.pi μ).prod (Measure.pi ν)) {y | f y = 0} = 0 := by
  obtain ⟨x, hxA, hx⟩ := h
  have hZ : MeasurableSet {p | f p = 0} :=
    (isClosed_eq (continuousOn_univ.1 hf.continuousOn) continuous_const).measurableSet
  have hae : Measure.pi ν {y | f (x.1, y) = 0} = 0 :=
    measure_pi_setOf_eq_zero (A := ∅) (by simp) (fun j _ => hν j)
      (fun y _ => (hf (x.1, y) (mem_univ _)).curry_right) ⟨x.2, by simp, hx⟩
  refine measure_prod_eq_zero_of_ae hZ ?_
  filter_upwards [ae_iff.2 (by simpa using hae : Measure.pi ν {y | ¬ f (x.1, y) ≠ 0} = 0)] with y hy
  exact measure_pi_setOf_eq_zero hA hAc (fun z _ => (hf (z, y) (mem_univ _)).curry_left)
    ⟨x.1, hxA, hy⟩

/-- **The zero set of a real analytic function that is not identically zero is null**, for Lebesgue
measure on a finite product of `ℝ`. -/
theorem volume_setOf_eq_zero {ι : Type*} [Fintype ι] {f : (ι → ℝ) → E}
    (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) : volume {x | f x = 0} = 0 := by
  obtain ⟨x, hx⟩ := h
  rw [volume_pi]
  exact measure_pi_setOf_eq_zero (A := ∅) (by simp) (fun _ _ => .rfl) hf ⟨x, by simp, hx⟩

/-- **The zero set of a real analytic function that is not identically zero is null**, for the
product of Lebesgue measures on two finite products of `ℝ`. -/
theorem prod_pi_volume_setOf_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) × (κ → ℝ) → E} (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) :
    ((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : κ => (volume : Measure ℝ))) {x | f x = 0} = 0 := by
  obtain ⟨x, hx⟩ := h
  exact measure_prod_pi_setOf_eq_zero (A := ∅) (by simp) (fun _ _ => .rfl) (fun _ => .rfl) hf
    ⟨x, by simp, hx⟩

/-- **The zero set of a real analytic function is null**, on `(ι → ℝ) × (κ → ℝ)`, for the product of
`δ₀` plus Lebesgue measure restricted to `s` on the coordinates of `ι` satisfying `p`, Lebesgue
measure restricted to `t` on the other coordinates of `ι`, and Lebesgue measure restricted to `u` on
those of `κ`, assuming that the function is nonzero somewhere on the face where the coordinates
satisfying `p` vanish. -/
theorem prod_pi_dirac_add_restrict_setOf_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Prop) [DecidablePred p] {s t u : Set ℝ} {f : (ι → ℝ) × (κ → ℝ) → E}
    (hf : AnalyticOnNhd ℝ f univ)
    (h : ∃ x : (ι → ℝ) × (κ → ℝ), (∀ i, p i → x.1 i = 0) ∧ f x ≠ 0) :
    ((Measure.pi fun i => if p i then Measure.dirac 0 + volume.restrict s
        else volume.restrict t).prod
      (Measure.pi fun _ : κ => volume.restrict u)) {x | f x = 0} = 0 := by
  have : ∀ i, SigmaFinite (if p i then Measure.dirac (0 : ℝ) + volume.restrict s
      else volume.restrict t) := fun i => by split_ifs <;> infer_instance
  refine measure_prod_pi_setOf_eq_zero (A := {i | p i}) (fun i hi => ?_) (fun i hi => ?_)
    (fun _ => Measure.absolutelyContinuous_of_le Measure.restrict_le_self) hf h
  · simp only [ite_eq_left (show p i from hi)]
    exact (Measure.AbsolutelyContinuous.rfl.add_right _).add_left
      ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).add_right' _)
  · simp only [ite_eq_right (show ¬ p i from hi)]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

end AnalyticOnNhd
