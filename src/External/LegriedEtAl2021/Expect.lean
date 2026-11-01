module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-!
# Expectations under discrete laws, and independent families

For a law `p : PMF α` and `f : α → ℝ≥0∞`, `expect p f` is the expectation of `f`. Values in `ℝ≥0∞` make Fubini free, and an expectation
can be `⊤`.

`piLaw p` is the law of an independent family, over a finite index type, and `iid J p` that of an i.i.d. family.

`PDom x' x t` is how two expectations of the proof of Theorem 1 of Legried, Molloy, Warnow and Roch compare: `x' ≤ x`, strictly when
the total `t` is positive and finite. `PDom.expect` says that it passes from the conditional expectations to the expectation.
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace External.LegriedEtAl2021

variable {α β γ : Type*}

/-- The expectation of a function with values in `[0, ⊤]` under a discrete law. -/
def expect (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

theorem expect_pure (a : α) (f : α → ℝ≥0∞) : expect (PMF.pure a) f = f a := by
  unfold expect
  rw [tsum_eq_single a fun b hb => by rw [PMF.pure_apply_of_ne a b hb, zero_mul]]
  rw [PMF.pure_apply_self, one_mul]

theorem expect_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    expect (p.bind q) f = expect p fun a => expect (q a) f := by
  unfold expect
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc]

theorem expect_const (p : PMF α) (c : ℝ≥0∞) : expect p (fun _ => c) = c := by
  unfold expect
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem expect_mono {p : PMF α} {f g : α → ℝ≥0∞} (h : ∀ a, p a ≠ 0 → f a ≤ g a) : expect p f ≤ expect p g := by
  unfold expect
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · gcongr
    exact h a ha

theorem expect_congr {p : PMF α} {f g : α → ℝ≥0∞} (h : ∀ a, p a ≠ 0 → f a = g a) : expect p f = expect p g :=
  le_antisymm (expect_mono fun a ha => (h a ha).le) (expect_mono fun a ha => (h a ha).ge)

theorem expect_add (p : PMF α) (f g : α → ℝ≥0∞) : expect p (fun a => f a + g a) = expect p f + expect p g := by
  unfold expect
  simp only [mul_add]
  exact ENNReal.tsum_add

theorem expect_mul_left (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) : expect p (fun a => c * f a) = c * expect p f := by
  unfold expect
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

theorem expect_mul_right (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) : expect p (fun a => f a * c) = expect p f * c := by
  simp only [mul_comm _ c]
  exact expect_mul_left p c f

theorem expect_sum {ι : Type*} (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    expect p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [expect_add, ih]

theorem expect_comm (p : PMF α) (q : PMF β) (f : α → β → ℝ≥0∞) :
    expect p (fun a => expect q (f a)) = expect q fun b => expect p fun a => f a b := by
  unfold expect
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

theorem exists_of_expect_ne_zero {p : PMF α} {f : α → ℝ≥0∞} (h : expect p f ≠ 0) : ∃ a, p a ≠ 0 ∧ f a ≠ 0 := by
  by_contra hne
  push Not at hne
  apply h
  unfold expect
  rw [ENNReal.tsum_eq_zero]
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · simp [hne a ha]

theorem ne_top_of_expect_ne_top {p : PMF α} {f : α → ℝ≥0∞} (h : expect p f ≠ ⊤) {a : α} (ha : p a ≠ 0) : f a ≠ ⊤ := by
  intro hf
  apply h
  unfold expect
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine le_trans ?_ (ENNReal.le_tsum a)
  simp [hf, ENNReal.mul_top ha]

theorem expect_lt {p : PMF α} {f g : α → ℝ≥0∞} (hfin : expect p f ≠ ⊤) (hle : ∀ a, p a ≠ 0 → f a ≤ g a) {a : α}
    (ha : p a ≠ 0) (hlt : f a < g a) : expect p f < expect p g := by
  unfold expect at *
  refine ENNReal.tsum_lt_tsum hfin (fun b => ?_) (i := a) ?_
  · by_cases hb : p b = 0
    · simp [hb]
    · gcongr
      exact hle b hb
  · have hpa : p a ≠ ⊤ := p.apply_ne_top a
    exact (ENNReal.mul_lt_mul_iff_right ha hpa).2 hlt

/-! ### How two expectations compare -/

/-- `x' ≤ x`, strictly when the total `t` is positive and finite. -/
def PDom (x' x t : ℝ≥0∞) : Prop := x' ≤ x ∧ (0 < t → t < ⊤ → x' < x)

/-- The comparison from the case that `x` exceeds a bound on `x'` by a positive amount. -/
theorem PDom.of_gap {x' x t y g : ℝ≥0∞} (hy : x' ≤ y) (hx : x = y + g) (hxt : x ≤ t) (hg : 0 < t → g ≠ 0) :
    PDom x' x t := by
  refine ⟨hy.trans (hx ▸ le_self_add), fun ht ht' => ?_⟩
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ht'.ne ((hx ▸ le_self_add : y ≤ x).trans hxt)
  rw [hx]
  exact hy.trans_lt (ENNReal.lt_add_right hyt (hg ht))

/-- A positive factor keeps the comparison. -/
theorem PDom.mul_left {x' x t : ℝ≥0∞} (h : PDom x' x t) (c : ℝ≥0∞) : PDom (c * x') (c * x) (c * t) := by
  refine ⟨by gcongr; exact h.1, fun h₁ h₂ => ?_⟩
  have hc : c ≠ 0 := fun hc => by simp [hc] at h₁
  have ht : t ≠ 0 := fun hc => by simp [hc] at h₁
  have hc' : c ≠ ⊤ := fun hc' => by simp [hc', ENNReal.top_mul ht] at h₂
  have ht' : t ≠ ⊤ := fun ht' => by simp [ht', ENNReal.mul_top hc] at h₂
  exact (ENNReal.mul_lt_mul_iff_right hc hc').2 (h.2 (pos_iff_ne_zero.2 ht) (lt_top_iff_ne_top.2 ht'))

/-- **The comparison passes from the conditional expectations to the expectation** (the law of total probability in the proof of
Theorem 1 of Legried, Molloy, Warnow and Roch). -/
theorem PDom.expect {p : PMF α} {F' F T : α → ℝ≥0∞} (h : ∀ a, p a ≠ 0 → PDom (F' a) (F a) (T a))
    (hT : ∀ a, p a ≠ 0 → F' a ≤ T a) : PDom (expect p F') (expect p F) (expect p T) := by
  refine ⟨expect_mono fun a ha => (h a ha).1, fun h₁ h₂ => ?_⟩
  obtain ⟨a, ha, hTa⟩ := exists_of_expect_ne_zero h₁.ne'
  have hfin : LegriedEtAl2021.expect p F' ≠ ⊤ := ne_top_of_le_ne_top h₂.ne (expect_mono hT)
  exact expect_lt hfin (fun b hb => (h b hb).1) ha
    ((h a ha).2 (pos_iff_ne_zero.2 hTa) (lt_top_iff_ne_top.2 (ne_top_of_expect_ne_top h₂.ne ha)))

/-! ### Independent families -/

/-- The sum over all families of a product is the product of the sums. -/
theorem tsum_prod_pi (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℝ≥0∞) :
    ∑' g : (∀ j, α j), ∏ j, f j (g j) = ∏ j, ∑' x, f j x := by
  refine Fintype.induction_empty_option (P := fun J _ => ∀ (α : J → Type) (f : ∀ j, α j → ℝ≥0∞),
    ∑' g : (∀ j, α j), ∏ j, f j (g j) = ∏ j, ∑' x, f j x) ?_ ?_ ?_ J α f
  · intro J J' _ e ih γ f
    let _ : Fintype J := Fintype.ofEquiv J' e.symm
    have h := ih (fun j => γ (e j)) (fun j => f (e j))
    rw [← (Equiv.piCongrLeft γ e).tsum_eq]
    refine Eq.trans ?_ (h.trans (Equiv.prod_comp e (fun j => ∑' x, f j x)))
    refine tsum_congr fun g => ?_
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Equiv.piCongrLeft_apply_apply]
  · intro γ f
    rw [tsum_eq_single (fun j => j.elim) fun g hg => (hg (funext fun j => j.elim)).elim]
    simp
  · intro J _ ih γ f
    rw [← (Equiv.piOptionEquivProd (β := γ)).symm.tsum_eq, Fintype.prod_option, ENNReal.tsum_prod']
    simp only [Fintype.prod_option, Equiv.piOptionEquivProd_symm_apply]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    rw [ih]

variable {J J' : Type} [Fintype J] [Fintype J']

/-- **The law of an independent family.** -/
def piLaw {α : J → Type} (p : ∀ j, PMF (α j)) : PMF (∀ j, α j) :=
  ⟨fun g => ∏ j, p j (g j), by
    rw [ENNReal.summable.hasSum_iff, tsum_prod_pi]
    simp [PMF.tsum_coe]⟩

theorem piLaw_apply {α : J → Type} (p : ∀ j, PMF (α j)) (g : ∀ j, α j) : piLaw p g = ∏ j, p j (g j) := rfl

theorem piLaw_ne_zero {α : J → Type} {p : ∀ j, PMF (α j)} {g : ∀ j, α j} (h : piLaw p g ≠ 0) (j : J) :
    p j (g j) ≠ 0 := by
  rw [piLaw_apply] at h
  exact Finset.prod_ne_zero_iff.1 h j (Finset.mem_univ j)

theorem piLaw_bind {α β : J → Type} (p : ∀ j, PMF (α j)) (q : ∀ j, α j → PMF (β j)) :
    piLaw (fun j => (p j).bind (q j)) = (piLaw p).bind fun s => piLaw fun j => q j (s j) := by
  ext g
  rw [PMF.bind_apply, piLaw_apply]
  simp only [PMF.bind_apply, piLaw_apply]
  rw [← tsum_prod_pi]
  exact tsum_congr fun s => Finset.prod_mul_distrib

theorem piLaw_pure {α : J → Type} (a : ∀ j, α j) : piLaw (fun j => PMF.pure (a j)) = PMF.pure a := by
  classical
  ext g
  rw [piLaw_apply, PMF.pure_apply]
  by_cases hg : g = a
  · subst hg
    simp [PMF.pure_apply]
  · simp only [hg, ↓reduceIte]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hg
    exact Finset.prod_eq_zero (Finset.mem_univ j) (PMF.pure_apply_of_ne _ _ hj)

/-- **The law of an i.i.d. family.** -/
abbrev iid (J : Type) [Fintype J] {α : Type} (p : PMF α) : PMF (J → α) := piLaw fun _ => p

/-- **Exchangeability**: reindexing an i.i.d. family keeps its law. -/
theorem expect_iid_equiv {α : Type} (e : J ≃ J') (p : PMF α) (f : (J' → α) → ℝ≥0∞) :
    expect (iid J' p) f = expect (iid J p) fun g => f (g ∘ e.symm) := by
  unfold expect
  rw [← (Equiv.arrowCongr e (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun g => ?_
  congr 1
  rw [piLaw_apply, piLaw_apply, ← Equiv.prod_comp e]
  simp [Equiv.arrowCongr]

/-- **An independent family of i.i.d. families is an i.i.d. family over the disjoint union of the index sets.** -/
theorem expect_piLaw_sigma {α : Type} {I : J → Type} [∀ j, Fintype (I j)] (p : PMF α)
    (G : (∀ j, I j → α) → ℝ≥0∞) :
    expect (piLaw fun j => iid (I j) p) G = expect (iid (Σ j, I j) p) fun h => G fun j i => h ⟨j, i⟩ := by
  unfold expect
  rw [← (Equiv.piCurry fun (j : J) (_ : I j) => α).tsum_eq]
  refine tsum_congr fun h => ?_
  congr 1
  rw [piLaw_apply, piLaw_apply]
  simp only [piLaw_apply, Equiv.piCurry_apply]
  rw [Fintype.prod_sigma]
  rfl

end External.LegriedEtAl2021
