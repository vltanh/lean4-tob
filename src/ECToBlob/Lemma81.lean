module

public import Basic.Testing.Tails

/-!
# ECToBlob §8: Lemma 8.1
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.QuartetTests Filter Topology

namespace ECToBlob

/-- **Lemma 8.1** (`ecto:lem8_1`). For each `K ≥ 1` and `ε > 0` there is `0 < δ < 1/2` such that for any
at most `K` possibly dependent asymptotically uniform random variables in `[0, 1]` there is `M` with
`P(all lie in [δ, 1 - δ]) > 1 - ε` for `n > M`. -/
theorem lemma8_1 (K : ℕ) (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
    ∀ {Γ ι : Type*} [Fintype Γ] [Fintype ι] (dist : Γ → ℝ) (p : ι → (n : ℕ) → (Fin n → Γ) → ℝ),
      IsDist dist → Fintype.card ι ≤ K → (∀ i n ω, 0 ≤ p i n ω ∧ p i n ω ≤ 1) →
      (∀ i, AsymptoticallyUniform dist (p i)) →
      ∃ M : ℕ, ∀ n, M < n →
        1 - ε < iidProb dist n fun ω => ∀ i, δ ≤ p i n ω ∧ p i n ω ≤ 1 - δ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  -- the paper assumes `ε ≤ 1` and takes `δ = ε/(4K)`
  refine ⟨min ε 1 / (4 * K), by positivity, ?_, ?_⟩
  · have h1 : min ε 1 / (4 * K) ≤ 1 / (4 * 1) :=
      div_le_div₀ zero_le_one (min_le_right _ _) (by norm_num) (by linarith)
    linarith
  intro Γ ι _ _ dist p hd hcard _ hunif
  set δ := min ε 1 / (4 * K) with hδ_def
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by
    have h1 : min ε 1 / (4 * K) ≤ 1 / (4 * 1) :=
      div_le_div₀ zero_le_one (min_le_right _ _) (by norm_num) (by linarith)
    linarith
  -- the sum of the probabilities of the bad events tends to `2 δ k`
  have hlim : Tendsto (fun n => ∑ i, (iidProb dist n (fun ω => p i n ω ≤ δ) +
      (1 - iidProb dist n fun ω => p i n ω ≤ 1 - δ))) atTop (𝓝 (∑ _i : ι, (δ + (1 - (1 - δ))))) :=
    tendsto_finsetSum _ fun i _ => (hunif i δ hδ0.le (by linarith)).add
      (tendsto_const_nhds.sub (hunif i (1 - δ) (by linarith) (by linarith)))
  have hbound : (∑ _i : ι, (δ + (1 - (1 - δ)))) < ε := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≤ K := by exact_mod_cast hcard
    have h1 : (Fintype.card ι : ℝ) * (δ + (1 - (1 - δ))) ≤ K * (2 * δ) := by
      have : δ + (1 - (1 - δ)) = 2 * δ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    have h2 : (K : ℝ) * (2 * δ) = min ε 1 / 2 := by
      rw [hδ_def]
      field_simp
      ring
    have h3 : min ε 1 / 2 < ε := by
      have := min_le_left ε 1
      linarith
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hbound))
  refine ⟨M, fun n hn => ?_⟩
  have hsum := hM n hn.le
  -- the union bound
  have hunion := iidProb_exists_le hd (fun i (ω : Fin n → Γ) =>
    ¬ (δ ≤ p i n ω ∧ p i n ω ≤ 1 - δ))
  have hterm : ∀ i, iidProb dist n (fun ω => ¬ (δ ≤ p i n ω ∧ p i n ω ≤ 1 - δ)) ≤
      iidProb dist n (fun ω => p i n ω ≤ δ) +
        (1 - iidProb dist n fun ω => p i n ω ≤ 1 - δ) := by
    intro i
    rw [← iidProb_not hd]
    refine (iidProb_mono hd ?_).trans (iidProb_or_le hd _ _)
    intro ω hω
    by_cases h : p i n ω ≤ δ
    · exact Or.inl h
    · refine Or.inr fun h' => hω ⟨(not_le.1 h).le, h'⟩
  have hsum2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  have hnot : iidProb dist n (fun ω => ∃ i, ¬ (δ ≤ p i n ω ∧ p i n ω ≤ 1 - δ)) =
      1 - iidProb dist n fun ω => ∀ i, δ ≤ p i n ω ∧ p i n ω ≤ 1 - δ := by
    rw [← iidProb_not hd]
    simp only [not_forall]
  rw [hnot] at hunion
  linarith

end ECToBlob
