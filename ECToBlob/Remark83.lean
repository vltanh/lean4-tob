module

public import External.AllmanBanosRhodes2019.Proposition9

/-!
# ECToBlob Remark 8.3

"The argument in the proof of Theorem 8.2 is easily adapted to strengthen the consistency results for the NANUQ [1]
and TINNiK [5] algorithms, which use quartet hypothesis tests in a similar way (though without combining p-values).
This makes explicit some valid choices of sequences of test levels for those algorithms."
(`notes/paper2026/paper.txt`, lines 1179-1182.)

The levels are those of the proof of Theorem 8.2, `alphaSeq` and `betaSeq`, which depend on nothing about the network.
The argument of that proof is: under the null, the p-value does not collapse, so it stays above any level tending to
`0`; off the null, the statistic grows linearly, so that the p-value is exponentially small, and it falls below any
level with `log(1/α_n) = o(n)`. Without combining, there is one p-value per test.

* NANUQ: `remark83_nanuq_levels`, `remark83_nanuq`, on the classes of all sets of four taxa and the distance of Step
  3, at their population values. No hypothesis on the parameters is needed. `remark83_nanuq_network`,
  `remark83_nanuq_fixed_beta` and `remark83_nanuq_generic` compare them with the network, under the hypotheses of the
  source's Theorem 36, on a binary level-1 network. Its Proposition 9 is proved
  (`External.AllmanBanosRhodes2019.proposition9`).
* What `β_n → 0` does: off the centroid nothing changes, since `log(1/β_n) = o(n)`. At the centroid, the star test's
  p-value is asymptotically uniform, so that it rejects with probability `→ β` at a fixed `β`, and with probability `→
  0` at `β_n → 0`, so the class there is a star tree with probability tending to one (`remark83_nanuq_star`). That is
  right at a trivial 4-blob, which a binary network does not have. At a `3₂`-cycle at the centroid it is the
  population value and not the network's class (`External.AllmanBanosRhodes2019.tendsto_ne_of_centroid`,
  `External.AllmanBanosRhodes2019.ThreeTwo.networkClass_N₃`). This occurs on a null set of parameters of a binary
  network (`remark83_nanuq_generic`), and neither a fixed `β` nor `β_n → 0` avoids it.
* TINNiK: `TINNiK.theorem4_explicit` has the level `α_m`, for fixed `β`. `remark83_tinnik` has `betaSeq` too, and
  `remark83_tinnik_t3` is the same for the T3 option.

The source of NANUQ is in `External/AllmanBanosRhodes2019/`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open External.AllmanBanosRhodes2019
open scoped Classical

namespace ECToBlob

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-! ### The levels of the proof of Theorem 8.2 -/

private theorem alphaSeq_pos (n : ℕ) : 0 < alphaSeq n := QuartetTests.chiSqOneTail_pos _

private theorem betaSeq_pos (n : ℕ) : 0 < betaSeq n := Real.exp_pos _

private theorem tendsto_alphaSeq₀ : Tendsto alphaSeq atTop (𝓝 0) := QuartetTests.tendsto_chiSqOneTail_log

private theorem tendsto_log_alphaSeq : Tendsto (fun n : ℕ => Real.log (alphaSeq n) / n) atTop (𝓝 0) :=
  QuartetTests.tendsto_log_chiSqOneTail_log

private theorem tendsto_betaSeq₀ : Tendsto betaSeq atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => -(Real.log n / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num))
  refine (Real.tendsto_exp_atBot.comp h).congr fun n => ?_
  simp [betaSeq, chiSqTwoTail, neg_div]

private theorem tendsto_log_betaSeq₀ : Tendsto (fun n : ℕ => Real.log (betaSeq n) / n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h' := (h.comp tendsto_natCast_atTop_atTop).const_mul (-(1 / 2) : ℝ)
  rw [mul_zero] at h'
  refine h'.congr fun n => ?_
  simp only [betaSeq, chiSqTwoTail, Real.log_exp, Function.comp, pow_one, one_mul, add_zero]
  ring

/-! ### NANUQ -/

section Nanuq

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-- Remark 8.3 for NANUQ, for any levels `α_n, β_n → 0` with `log(1/α_n), log(1/β_n) = o(n)`, for any distribution on
binary gene trees with positive concordance factors: with probability tending to one, Step 2 gives the population
class of all sets of four taxa, and so the distance of Step 3 is its population value. -/
theorem remark83_nanuq_levels (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides)
    (hpos : ∀ r, 0 < displayCF dist sides r) {α β : ℕ → ℝ} (hα : ∀ n, 0 < α n) (hα₀ : Tendsto α atTop (𝓝 0))
    (hαlog : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0)) (hβ : ∀ n, 0 < β n)
    (hβ₀ : Tendsto β atTop (𝓝 0)) (hβlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0))
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb dist n fun ω =>
      (∀ q : Finset X, q.card = 4 →
        classify mlT mlC (α n) (β n) (quartetCount sides ω) q = cfClass (displayCF dist sides) q) ∧
      nanuqDistance (classify mlT mlC (α n) (β n) (quartetCount sides ω)) =
        nanuqDistance (cfClass (displayCF dist sides))) atTop (𝓝 1) :=
  tendsto_iidProb_of_imp hd (Eventually.of_forall fun _ _ hω => ⟨hω, nanuqDistance_congr hω⟩)
    (tendsto_classify_eq_cfClass hd hs hpos hα₀ (rejectsOffNull_of_log hd hs hα hαlog) hβ hβlog (Or.inr hβ₀) hmlT hmlC)

end Nanuq

/-- **Remark 8.3 for NANUQ** (`ecto:remark8_3`), at the sequences `alphaSeq`, `betaSeq` of the proof of Theorem 8.2,
which depend on nothing about the network. For a phylogenetic network at any valid parameters: with probability
tending to one, the classification of all sets of four taxa is right, as an estimate of its population value, and the
empirical NANUQ distance equals its population value.

The source's Theorem 36 has a sequence `α_m` that depends on the unknown limits of the statistic, and a fixed `β`. -/
theorem remark83_nanuq [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb (geneTreeDist N θ ρ) n fun ω =>
      (∀ q : Finset X, q.card = 4 →
        classify mlT mlC (alphaSeq n) (betaSeq n) (quartetCount unroot ω) q = cfClass (nmscCF N θ ρ) q) ∧
      nanuqDistance (classify mlT mlC (alphaSeq n) (betaSeq n) (quartetCount unroot ω)) =
        nanuqDistance (cfClass (nmscCF N θ ρ))) atTop (𝓝 1) :=
  remark83_nanuq_levels (isDist_geneTreeDist hN hθ hρ) (displaysOne_nmsc hN) (fun r => nmscCF_pos hN hθ hρ r)
    alphaSeq_pos tendsto_alphaSeq₀ tendsto_log_alphaSeq betaSeq_pos tendsto_betaSeq₀ tendsto_log_betaSeq₀ hmlT hmlC

/-- At a trivial 4-blob, at these levels, Step 2 says "star tree", with probability tending to one, on any network.
With a fixed `β` it says so with probability tending only to `1 - β`
(`External.AllmanBanosRhodes2019.tendsto_star_le_of_centroid`). -/
theorem remark83_nanuq_star [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {q : Finset X} (hq : q.card = 4)
    (ht : HasTrivialFourBlob N q) {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hmlT : IsMaxCountSelection mlT) (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb (geneTreeDist N θ ρ) n fun ω =>
      classify mlT mlC (alphaSeq n) (betaSeq n) (quartetCount unroot ω) q = .star) atTop (𝓝 1) := by
  have huni : ∀ r ∈ treesOn q, nmscCF N θ ρ r = 1 / 3 := NMSC.trivial_uniform hN hθ hρ q hq ht
  refine tendsto_iidProb_of_imp (isDist_geneTreeDist hN hθ hρ) (Eventually.of_forall fun n ω hω => ?_)
    (remark83_nanuq hN hθ hρ hmlT hmlC)
  rw [hω.1 q hq, cfClass_eq_star huni]

/-- **The strengthening on the network**: under the hypotheses of the source's Theorem 36, with the correction of
`External.AllmanBanosRhodes2019.theorem36`, at the sequences `alphaSeq`, `betaSeq`, Step 2 gives the network's class
of all sets of four taxa, and the distance of Step 3 is the theoretical distance, with probability tending to one. -/
theorem remark83_nanuq_network [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hBin : N.IsBinary) (hLevel : TOBQMC.IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hmlT : IsMaxCountSelection mlT) (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb (geneTreeDist N θ ρ) n fun ω =>
      (∀ q : Finset X, q.card = 4 →
        classify mlT mlC (alphaSeq n) (betaSeq n) (quartetCount unroot ω) q = networkClass N q) ∧
      nanuqDistance (classify mlT mlC (alphaSeq n) (betaSeq n) (quartetCount unroot ω)) = networkDistance N)
      atTop (𝓝 1) :=
  tendsto_classify_eq_networkClass hN hLevel hθ hρ (proposition9 hN hBin hLevel hθ hρ) h32 hcen tendsto_alphaSeq₀
    (rejectsOffNull_of_log (isDist_geneTreeDist hN hθ hρ) (displaysOne_nmsc hN) alphaSeq_pos tendsto_log_alphaSeq)
    betaSeq_pos tendsto_log_betaSeq₀ hmlT hmlC

/-- **Theorem 36 with an explicit sequence**: under the same hypotheses, the sequence `α_m` of the source's theorem
can be `alphaSeq`, for any fixed `β > 0`. -/
theorem remark83_nanuq_fixed_beta [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hBin : N.IsBinary) (hLevel : TOBQMC.IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) {β : ℝ} (hβ : 0 < β)
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hmlT : IsMaxCountSelection mlT) (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb (geneTreeDist N θ ρ) n fun ω =>
      (∀ q : Finset X, q.card = 4 →
        classify mlT mlC (alphaSeq n) β (quartetCount unroot ω) q = networkClass N q) ∧
      nanuqDistance (classify mlT mlC (alphaSeq n) β (quartetCount unroot ω)) = networkDistance N)
      atTop (𝓝 1) :=
  tendsto_classify_eq_networkClass hN hLevel hθ hρ (proposition9 hN hBin hLevel hθ hρ) h32 hcen tendsto_alphaSeq₀
    (rejectsOffNull_of_log (isDist_geneTreeDist hN hθ hρ) (displaysOne_nmsc hN) alphaSeq_pos tendsto_log_alphaSeq)
    (β := fun _ => β) (fun _ => hβ) (tendsto_log_const_div β) hmlT hmlC

/-- **For generic parameters**, the hypothesis of Theorem 36 as printed suffices at these sequences: a binary network
has no concordance factor at the centroid off a null set of its parameters, so that `β_n → 0` costs nothing there. -/
theorem remark83_nanuq_generic [Fintype V] [Fintype E] [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hBin : N.IsBinary) (hLevel : TOBQMC.IsLevelOne N) :
    ∃ A : Set (MetricData E), External.AllmanEtAl2023.IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → ThreeTwoTreelike N (nmscCF N θ 0) →
      ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun n => iidProb (geneTreeDist N θ 0) n fun ω =>
          nanuqDistance (classify mlT mlC (alphaSeq n) (betaSeq n) (quartetCount unroot ω)) = networkDistance N)
          atTop (𝓝 1) := by
  refine ⟨_, TINNiK.isGenericNull_centroid hN hBin, fun θ hθ hA h32 mlT mlC hmlT hmlC => ?_⟩
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hcen : TINNiK.NoCentroidCF (nmscCF N θ 0) := by
    by_contra hn
    exact hA ⟨hθ, hn⟩
  exact tendsto_iidProb_of_imp (isDist_geneTreeDist hN hθ hρ) (Eventually.of_forall fun n ω hω => hω.2)
    (remark83_nanuq_network hN hBin hLevel hθ hρ h32 hcen hmlT hmlC)

/-! ### TINNiK -/

section Tinnik

/-- When the star test rejects on all sets of four taxa at two levels, the sets judged B-quartets are the same at
both. -/
private theorem testedB_congr {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β β' : ℝ}
    {c : QuartetTree X → ℝ} (h : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β)
    (h' : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β') : testedB ml α β c = testedB ml α β' c := by
  ext q
  simp only [testedB, Set.mem_ofPred_eq]
  refine and_congr_right fun hq => or_congr ?_ Iff.rfl
  exact ⟨fun hle => absurd (h q hq) (not_lt.2 hle), fun hle => absurd (h' q hq) (not_lt.2 hle)⟩

private theorem tinnik_congr {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β β' δ : ℝ}
    {M : TreeBuilder X} {c : QuartetTree X → ℝ} (h : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β)
    (h' : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β') : tinnik ml α β δ M c = tinnik ml α β' δ M c := by
  have hB := testedB_congr (ml := ml) (α := α) h h'
  have hT : testedT ml α β c = testedT ml α β' c := by
    simp only [testedT, hB]
  rw [TINNiK.tinnik_eq_tinnikOf, TINNiK.tinnik_eq_tinnikOf, hB, hT]

private theorem testedBT3_congr {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β β' : ℝ}
    {c : QuartetTree X → ℝ} (h : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β)
    (h' : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β') :
    TINNiK.testedBT3 ml α β c = TINNiK.testedBT3 ml α β' c := by
  ext q
  simp only [TINNiK.testedBT3, Set.mem_ofPred_eq]
  refine and_congr_right fun hq => or_congr ?_ Iff.rfl
  exact ⟨fun hle => absurd (h q hq) (not_lt.2 hle), fun hle => absurd (h' q hq) (not_lt.2 hle)⟩

private theorem tinnikT3_congr {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β β' δ : ℝ}
    {M : TreeBuilder X} {c : QuartetTree X → ℝ} (h : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β)
    (h' : ∀ q : Finset X, q.card = 4 → starPValue .lrt c q < β') :
    TINNiK.tinnikT3 ml α β δ M c = TINNiK.tinnikT3 ml α β' δ M c := by
  have hB := testedBT3_congr (ml := ml) (α := α) h h'
  have hT : TINNiK.testedTT3 ml α β c = TINNiK.testedTT3 ml α β' c := by
    simp only [TINNiK.testedTT3, hB]
  simp only [TINNiK.tinnikT3, hB, hT]

/-- The star test rejects on all sets of four taxa, at the level `β_n`, off the centroid. -/
private theorem tendsto_star_all {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}
    (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) (hcen : TINNiK.NoCentroidCF (displayCF dist sides))
    {β : ℕ → ℝ} (hβ : ∀ n, 0 < β n) (hβlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω => ∀ q : Finset X, q.card = 4 →
      starPValue .lrt (quartetCount sides ω) q < β n) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω q hq => hω ⟨q, hq⟩)
    (tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
      (fun q n ω => starPValue .lrt (quartetCount sides ω) q.val < β n)
      fun q => tendsto_starPValue_lt hd hs q.property (hcen q.val q.property) hβ hβlog)

/-- **Remark 8.3 for TINNiK** (`ecto:remark8_3`), with both levels explicit: at the sequences `alphaSeq`, `betaSeq`.
`TINNiK.theorem4_explicit` has `alphaSeq` and a fixed `β`. Off the centroid, which CF-detectability excludes, the star
test rejects at all these levels, so that the level makes no difference to the output. -/
theorem remark83_tinnik [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0)) {δ : ℝ} (hδ₂ : δ < 2)
    {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : IsMLSelection ml) :
    Tendsto (fun m : ℕ => iidProb (geneTreeDist N θ 0) m fun ω =>
      tinnik ml (alphaSeq m) (betaSeq m) δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd := isDist_geneTreeDist (N := N) hN hθ hρ
  have hs := displaysOne_nmsc (θ := θ) (ρ := 0) hN
  have hcen := TINNiK.noCentroidCF_of_cfDetectable hdet
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd (TINNiK.theorem4_explicit hN hX hθ hdet one_pos hδ₂ hM hml)
      (TINNiK.tendsto_iidProb_and hd (tendsto_star_all hd hs hcen betaSeq_pos tendsto_log_betaSeq₀)
        (tendsto_star_all hd hs hcen (β := fun _ => 1) (fun _ => one_pos) (tendsto_log_const_div 1))))
  obtain ⟨h₁, h₂, h₃⟩ := hω
  exact (tinnik_congr h₂ h₃).trans h₁

/-- Remark 8.3 for the T3 option of TINNiK, with both levels explicit, under the hypothesis of
`TINNiK.theorem4T3_explicit`. -/
theorem remark83_tinnik_t3 [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) {θ : MetricData E} (hθ : N.IsMetric θ)
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ 0))
    (hno : TINNiK.NoAnomalousQuartets N (nmscCF N θ 0)) {δ : ℝ} (hδ₂ : δ < 2)
    {M : TreeBuilder X} (hM : IsExactBuilder M)
    {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hml : TINNiK.IsT3MLSelection ml) :
    Tendsto (fun m : ℕ => iidProb (geneTreeDist N θ 0) m fun ω =>
      TINNiK.tinnikT3 ml (alphaSeq m) (betaSeq m) δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := by
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd := isDist_geneTreeDist (N := N) hN hθ hρ
  have hs := displaysOne_nmsc (θ := θ) (ρ := 0) hN
  have hcen := TINNiK.noCentroidCF_of_cfDetectable hdet
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd (TINNiK.theorem4T3_explicit hN hX hθ hdet hno one_pos hδ₂ hM hml)
      (TINNiK.tendsto_iidProb_and hd (tendsto_star_all hd hs hcen betaSeq_pos tendsto_log_betaSeq₀)
        (tendsto_star_all hd hs hcen (β := fun _ => 1) (fun _ => one_pos) (tendsto_log_const_div 1))))
  obtain ⟨h₁, h₂, h₃⟩ := hω
  exact (tinnikT3_congr h₂ h₃).trans h₁

end Tinnik

end ECToBlob
