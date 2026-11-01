module

public import TINNiK.Statistics.AppendixC

/-!
# TINNiK Appendix C.1: the maximum likelihood estimate on the open cut model

E31 of the report. Definition 7 of the paper defines the cut model inside the open simplex `Δ²` (`GeneratingCutModel`), and
Appendix C.1 says that its maximum likelihood estimate "is found by computing the maximum of the trinomial likelihood constrained
to each of the 3 line segments", with the maximizer on the vertical line `(m₁/m, (m-m₁)/(2m), (m-m₁)/(2m))`.

At counts in one coordinate, such as `(1, 0, 0)`, that point has zero entries, so it is off the model
(`cutLineMLE_not_generatingCutModel`), and the likelihood has no maximum on the model at all
(`not_exists_generatingCutModel_maximizer`): its supremum there is `1` (`isLUB_likelihood_generatingCutModel`), which is not attained.
That is what the formalization's closed simplex repairs (`cutLineMLE_maximizes`). Not every count with a zero fails: at `(4, 1, 0)` the
maximizer on the line `p₂ = p₃` is interior and beats the other two lines, by a computation not formalized here. No result of the
paper is affected.
-/

@[expose] public noncomputable section

namespace TINNiK

private lemma add_one_ne_self (i : Fin 3) : i + 1 ≠ i := by
  revert i
  decide

/-- The counts `n` in the coordinate `i` and zero in the others. -/
def concentratedCounts (i : Fin 3) (n : ℕ) : Counts := fun j => if j = i then n else 0

theorem likelihood_concentratedCounts (i : Fin 3) (n : ℕ) (p : Coordinates) :
    likelihood (concentratedCounts i n) p = p i ^ n := by
  unfold likelihood concentratedCounts
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem sampleSize_concentratedCounts (i : Fin 3) (n : ℕ) : sampleSize (concentratedCounts i n) = n := by
  unfold sampleSize concentratedCounts
  simp

/-- The point of the model on the line of `i` with entries `1 - 2ε` at `i` and `ε` elsewhere. -/
def linePoint (i : Fin 3) (ε : ℝ) : Coordinates := fun j => if j = i then 1 - 2 * ε else ε

theorem linePoint_self (i : Fin 3) (ε : ℝ) : linePoint i ε i = 1 - 2 * ε := by simp [linePoint]

theorem linePoint_generatingCutModel (i : Fin 3) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    GeneratingCutModel (linePoint i ε) := by
  refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
  · unfold linePoint
    split_ifs <;> linarith
  · fin_cases i <;> simp [linePoint, Fin.sum_univ_three] <;> ring
  · rw [isCut_iff_onCutLine]
    refine ⟨i, fun j k hj hk => ?_⟩
    simp [linePoint, hj, hk]

/-- On the open simplex, every entry is below one. -/
theorem OpenSimplex.lt_one {p : Coordinates} (hp : OpenSimplex p) (i : Fin 3) : p i < 1 := by
  obtain ⟨hpos, hsum⟩ := hp
  obtain ⟨j, hj⟩ : ∃ j, j ≠ i := ⟨i + 1, add_one_ne_self i⟩
  have hle : p i + p j ≤ ∑ k, p k := by
    rw [← Finset.sum_pair hj.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => (hpos k).le
  linarith [hpos j]

/-- **The maximizer printed in Appendix C.1 is off the cut model of Definition 7** (`tinnik:cut_line_mle_open`, E31 of the report):
at the counts `(n, 0, 0)` it is the vertex of the simplex. -/
theorem cutLineMLE_not_generatingCutModel (i : Fin 3) (n : ℕ) :
    ¬ GeneratingCutModel (cutLineMLE (concentratedCounts i n) i) := by
  rintro ⟨⟨hpos, -⟩, -⟩
  obtain ⟨j, hj⟩ : ∃ j, j ≠ i := ⟨i + 1, add_one_ne_self i⟩
  have hother : otherCount (concentratedCounts i n) i = 0 := by
    have h := otherCount_add (concentratedCounts i n) i
    rw [sampleSize_concentratedCounts] at h
    simp only [concentratedCounts, ite_true] at h
    omega
  have := hpos j
  simp [cutLineMLE, hj, hother] at this

/-- **The likelihood at counts in one coordinate has supremum `1` on the cut model of Definition 7**
(`tinnik:cut_model_sup`, E31 of the report). -/
theorem isLUB_likelihood_generatingCutModel (i : Fin 3) (n : ℕ) :
    IsLUB (likelihood (concentratedCounts i n) '' {p | GeneratingCutModel p}) 1 := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    rw [likelihood_concentratedCounts]
    exact pow_le_one₀ (hp.1.1 i).le (hp.1.lt_one i).le
  · intro b hb
    by_contra hlt
    have hb1 : b < 1 := not_le.mp hlt
    -- a continuity argument: `(1 - 2ε)ⁿ` tends to `1` as `ε → 0`
    have hcont : Filter.Tendsto (fun ε : ℝ => (1 - 2 * ε) ^ n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h : Continuous fun ε : ℝ => (1 - 2 * ε) ^ n := by fun_prop
      have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have hev := hcont.eventually (lt_mem_nhds hb1)
    have hsmall : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
      Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨ε, hε, h0, h1⟩ := (hev.and hsmall).exists
    have hle := hb ⟨linePoint i ε, linePoint_generatingCutModel i h0 h1, rfl⟩
    rw [likelihood_concentratedCounts, linePoint_self] at hle
    exact absurd hle (not_le.mpr hε)

/-- **Appendix C.1 on the open cut model: no maximum exists** (`tinnik:no_open_cut_mle`, E31 of the report). At the counts `n > 0`
in one coordinate, for example `(1, 0, 0)`, no point of the cut model of Definition 7 maximizes the trinomial likelihood. -/
theorem not_exists_generatingCutModel_maximizer (i : Fin 3) {n : ℕ} (hn : 0 < n) :
    ¬ ∃ p, GeneratingCutModel p ∧ ∀ q, GeneratingCutModel q →
      likelihood (concentratedCounts i n) q ≤ likelihood (concentratedCounts i n) p := by
  rintro ⟨p, hp, hmax⟩
  have hlub := isLUB_likelihood_generatingCutModel i n
  have hub : (1 : ℝ) ≤ likelihood (concentratedCounts i n) p :=
    hlub.2 (by
      rintro _ ⟨q, hq, rfl⟩
      exact hmax q hq)
  rw [likelihood_concentratedCounts] at hub
  have hlt : p i ^ n < 1 := pow_lt_one₀ (hp.1.1 i).le (hp.1.lt_one i) hn.ne'
  exact absurd hub (not_le.mpr hlt)

/-- The case the report names: the counts `(1, 0, 0)`. -/
theorem not_exists_generatingCutModel_maximizer_one_zero_zero :
    ¬ ∃ p, GeneratingCutModel p ∧ ∀ q, GeneratingCutModel q →
      likelihood ![1, 0, 0] q ≤ likelihood ![1, 0, 0] p := by
  have h : (![1, 0, 0] : Counts) = concentratedCounts 0 1 := by
    funext j
    fin_cases j <;> simp [concentratedCounts]
  rw [h]
  exact not_exists_generatingCutModel_maximizer 0 one_pos

end TINNiK
