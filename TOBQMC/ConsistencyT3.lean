module

public import TINNiK.T3
public import TOBQMC.Consistency

/-!
# TOB-QMC §4.3: statistical consistency with the T3 option

TOB-QMC's oracle for treelikeness is "TINNiK's hypothesis tests", with the T3 test the default ("the T3 option is the default in
TINNiK due to its strong empirical performance", v5, lines 121–122). `TOBQMC.consistency` treats the star and cut tests. This file
gives the same claim with the T3 option, under the paper's conditions 5, 6a and 6b.

## Which assumption the T3 option needs

Condition 6b (lines 110–112) is class 1 quartet-nonanomaly: on *every* treelike four-taxon subset, the topology of the highest
expected concordance factor is the tree of blobs of the subnetwork (`TINNiK.NoAnomalousQuartets`). Condition 4 is T-quartet-nonanomaly
(`IsTQuartetNonanomalous`), on the subsets the tree of blobs of the whole network resolves. The T3 test does not reject exactly when
the concordance factor is on its half-lines, so `TINNiK.tests_correct_t3` needs the inequality on all treelike subsets, 6b. The three
classes of subsets (E21 of the report):

* a subset with no cut-edge split on its induced network: the T3 test rejects by 6a, which says more than is needed (off the T3
  model suffices, `consistencyT3_of_offModel`);
* a subset that the tree of blobs resolves: condition 4 applies, and the test does not reject;
* a treelike subset that the tree of blobs does not resolve: condition 4 says nothing. At level 1 nothing needs to be assumed: the split
  has the strictly largest concordance factor (`Level1.nmscCF_lt_of_not_displays`).

So at level 1, 6b and condition 4 are equivalent (`noAnomalousQuartets_iff_tQuartetNonanomalous`). The paper's stated assumptions suffice,
and 6b adds nothing to condition 4. On any network, 6b implies condition 4 (`isTQuartetNonanomalous_of_noAnomalous`); that condition 4 implies
6b is proved here only at level 1. Beyond level 1 an anomalous subset of the third class would make the tests wrong on it
(`TINNiK.tendsto_mem_testedBT3_of_anomalous`), but TINNiK's output needs only condition 4 (`TINNiK.theorem4T3_of_tQuartet`).

## Main results

* `consistencyT3`: the consistency claim with the T3 option, under conditions 4, 5, 6a.
* `consistencyT3_of_noAnomalous`: the same under conditions 5, 6a, 6b, as the paper lists them.
* `consistencyT3_of_offModel`: the same with 6a weakened to what the T3 test uses.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The output of the method with the T3 option: from the tree `B`, contract the edges where the tests judge a 4-taxon set of the
disjoint cover `Q` to be non-treelike. Parallel to `tobqmc`. -/
def tobqmcT3 (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (B : Finset (Finset X)) (Q : Finset X → Finset (Finset X)) : Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A, Y ∈ TINNiK.testedBT3 ml α β c)

/-- Condition 6b (class 1 quartet-nonanomaly) gives condition 4 (T-quartet-nonanomaly), on any network, as the paper says: "This
assumption is no more restrictive than the one made by TINNiK (T3 option)" (v5, line 421). A quartet tree of the tree of blobs is a
cut-edge split of the induced network. -/
theorem isTQuartetNonanomalous_of_noAnomalous {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    {p : QuartetTree X → ℝ} (h : TINNiK.NoAnomalousQuartets N p) : IsTQuartetNonanomalous N p :=
  fun s hs r hr => h s (External.AllmanEtAl2023.inducedCutSplit_of_displays hN hs) r hr

/-- **At level 1, conditions 4 and 6b are equivalent.** The direction from 4 to 6b is `Level1.nmscCF_lt_of_inducedCutSplit`, a fact
that the paper does not state. So 6b is no extra assumption on a level-1 network. -/
theorem noAnomalousQuartets_iff_tQuartetNonanomalous [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    TINNiK.NoAnomalousQuartets N (nmscCF N θ ρ) ↔ IsTQuartetNonanomalous N (nmscCF N θ ρ) :=
  ⟨isTQuartetNonanomalous_of_noAnomalous hN, fun hNon _ hs _ hr =>
    Level1.nmscCF_lt_of_inducedCutSplit hN hLevel hθ hρ hNon hs hr⟩

/-- What the T3 test needs holds under the paper's assumptions, for all four-taxon subsets of a level-1 network: non-treelike subsets by
`hOff`, which 6a implies; subsets the tree of blobs resolves by condition 4 and exchangeability; and the other treelike subsets by
`Level1.nmscCF_lt_of_not_displays`, with no assumption. -/
theorem t3Detectable_of_level1 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hOff : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → ¬ IsT3Null (nmscCF N θ ρ) q) :
    TINNiK.T3Detectable N (nmscCF N θ ρ) :=
  ⟨fun _ hs => ⟨fun _ hr =>
      Level1.nmscCF_lt_of_inducedCutSplit hStd.phylogenetic hLevel hStd.metric hStd.rho hNon hs hr,
    NMSC.cut_alternatives hStd.phylogenetic hStd.metric hStd.rho _ hs⟩, hOff⟩

/-- The answer of Theorem 1 on counts `c`: every optimal solution of Weighted Quartet Consensus for `c` is a refinement of the tree of
blobs. As in `TOBQMC/Consistency.lean`, where it is private. -/
private def OptimaRefine {V E : Type*} (N : RootedNetwork V E X) (c : QuartetTree X → ℝ) : Prop :=
  ∀ B, IsBinaryTree B → (∀ T, IsBinaryTree T → quartetScore c T ≤ quartetScore c B) →
    treeOfBlobs N ⊆ B

/-- The counts of the first `k` terms of a sequence of gene trees. As in `TOBQMC/Consistency.lean`, where it is private. -/
private theorem geneCount_coords (k : ℕ) (ω : ℕ → Finset (Finset X)) :
    geneCount (fun i ω => ω i) k ω = quartetCount unroot (fun i : Fin k => ω i) := by
  funext s
  simp only [geneCount, quartetCount]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun i => if Displays (unroot (ω i)) s then 1 else 0)]

/-- The coordinates of the independent sequence of draws from the NMSC are a gene tree sample. As in `TOBQMC/Consistency.lean`, where it
is private. -/
private theorem isGeneTreeSample_iidSeq {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    {θ : MetricData E} {ρ : ℝ} [MeasurableSpace (Finset (Finset X))]
    [MeasurableSingletonClass (Finset (Finset X))] (hd : IsDist (geneTreeDist N θ ρ)) :
    IsGeneTreeSample (Trinomial.iidSeq (geneTreeDist N θ ρ) hd) N θ ρ (fun i ω => ω i) := by
  have hpi : ∀ (s : Finset ℕ) (g : ℕ → Finset (Finset X)),
      Trinomial.iidSeq (geneTreeDist N θ ρ) hd (⋂ i ∈ s, (fun ω : ℕ → Finset (Finset X) => ω i) ⁻¹' {g i}) =
        ∏ i ∈ s, ENNReal.ofReal (geneTreeDist N θ ρ (g i)) := by
    intro s g
    have hset : (⋂ i ∈ s, (fun ω : ℕ → Finset (Finset X) => ω i) ⁻¹' {g i}) =
        Set.pi (s : Set ℕ) (fun i => {g i}) := by
      ext ω
      simp [Set.mem_pi]
    rw [hset, Trinomial.iidSeq, MeasureTheory.Measure.infinitePi_pi _
      (fun i _ => measurableSet_singleton (g i))]
    exact Finset.prod_congr rfl fun i _ => Trinomial.toPMF_singleton hd (g i)
  have hone : ∀ (i : ℕ) (g : Finset (Finset X)),
      Trinomial.iidSeq (geneTreeDist N θ ρ) hd ((fun ω : ℕ → Finset (Finset X) => ω i) ⁻¹' {g}) =
        ENNReal.ofReal (geneTreeDist N θ ρ g) := by
    intro i g
    have := hpi {i} (fun _ => g)
    simpa using this
  refine ⟨fun i g => measurable_pi_apply i (measurableSet_singleton g), fun s g => ?_, fun i g => ?_⟩
  · rw [hpi s g]
    exact Finset.prod_congr rfl fun i _ => (hone i (g i)).symm
  · rw [MeasureTheory.measureReal_def, hone, ENNReal.toReal_ofReal (hd.1 g)]

/-- **Theorem 1 for finite samples**, as in `TOBQMC/Consistency.lean`, where it is private. From `theorem1_optimal` on the independent
sequence, by continuity from below. -/
private theorem tendsto_optimaRefine {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    {θ : MetricData E} {ρ : ℝ} (hStd : StandardAssumptions N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    (hd : IsDist (geneTreeDist N θ ρ)) :
    Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
      OptimaRefine N (quartetCount unroot ω)) atTop (𝓝 1) := by
  let : MeasurableSpace (Finset (Finset X)) := ⊤
  have : MeasurableSingletonClass (Finset (Finset X)) := ⟨fun _ => trivial⟩
  set P := Trinomial.iidSeq (geneTreeDist N θ ρ) hd with hP
  have hae := theorem1_optimal hStd hNon hX P (fun i ω => ω i) (isGeneTreeSample_iidSeq hd)
  -- the events "for all later `k`"
  let A : ℕ → Set (ℕ → Finset (Finset X)) := fun K =>
    {ω | ∀ k, K ≤ k → OptimaRefine N (geneCount (fun i ω => ω i) k ω)}
  have hmono : Monotone A := fun K K' hKK ω hω k hk => hω k (hKK.trans hk)
  have hunion : P (⋃ K, A K) = 1 := by
    have h0 : ∀ᵐ ω ∂P, ω ∈ ⋃ K, A K := by
      filter_upwards [hae] with ω hω
      exact Set.mem_iUnion.mpr hω
    have := MeasureTheory.measure_congr (MeasureTheory.ae_eq_univ.mpr
      (MeasureTheory.ae_iff.mp h0))
    rw [this, MeasureTheory.measure_univ]
  have hlim : Tendsto (fun K => P (A K)) atTop (𝓝 1) := by
    have := MeasureTheory.tendsto_measure_iUnion_atTop (μ := P) hmono
    rwa [hunion] at this
  have hlim' : Tendsto (fun K => P.real (A K)) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    simpa [MeasureTheory.measureReal_def, Function.comp_def] using this
  have hprob : ∀ k, iidProb (geneTreeDist N θ ρ) k (fun ω => OptimaRefine N (quartetCount unroot ω)) =
      P.real {ω | OptimaRefine N (geneCount (fun i ω => ω i) k ω)} := by
    intro k
    rw [Trinomial.iidProb_eq_iidSeq hd]
    simp only [geneCount_coords]
    rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim' tendsto_const_nhds
    (fun k => ?_) (fun k => iidProb_le_one hd k _)
  rw [hprob k]
  exact MeasureTheory.measureReal_mono (fun ω hω => hω k le_rfl)

/-- The consistency claim of §4.3 with the T3 option, with the part of 6a that the T3 test uses: the concordance factors of the
non-treelike 4-taxon sets are off model T3. Condition 6a asks that they be non-cut, which the cut test needs: unlike it, the T3 test also
detects a 4-blob with a cut concordance factor `(p, q, q)`, `q > 1/3`. -/
theorem consistencyT3_of_offModel [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hOff : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → ¬ IsT3Null (nmscCF N θ ρ) q)
    (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), TINNiK.IsT3MLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  -- the tests are correct on all four-taxon subsets
  have hdet := t3Detectable_of_level1 hStd hLevel hNon hOff
  obtain ⟨α, hα₀, hαpos, hrej⟩ := TINNiK.exists_levels_t3 hN hStd.metric hStd.rho hdet
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve cover hcover => ?_⟩
  have htests := TINNiK.tests_correct_t3_of_t3Detectable hN hX hStd.metric hStd.rho hdet hα₀ hrej hβ hml
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd htests (tendsto_optimaRefine hStd hNon hX hd))
  obtain ⟨⟨hB, -⟩, hopt⟩ := hω
  obtain ⟨hbin, hmax⟩ := hsolve (quartetCount unroot ω)
  have hTB := hopt _ hbin hmax
  have hcov := hcover _ hbin
  -- so the method is the oracle's, on a refinement of the tree of blobs: Theorem 2
  rw [← theorem2 hN hStd.binary hLevel (IsBinaryTree.isUnrootedTree hbin) hTB _ hcov, tobqmcT3]
  congr 1
  refine Finset.filter_congr fun A hA => exists_congr fun Y => and_congr_right fun hYQ => ?_
  obtain ⟨s, -, rfl⟩ := (hcov A hA).around Y hYQ
  rw [hB]
  exact ⟨fun h => h.2, fun h => ⟨QuartetTree.card_taxa s, h⟩⟩

/-- **The consistency claim of §4.3 with the T3 option.** For a binary level-1 network under the standard
assumptions that is T-quartet-nonanomalous, whose non-treelike 4-taxon sets have distinct concordance factors (assumption 6a), there
are levels `α_k → 0` such that for any `β > 0`, any selection of maximum likelihood topologies on model T3, any solver of Weighted
Quartet Consensus and any selection of disjoint covers, the method with the T3 test on `k` independent gene trees returns the tree of
blobs with probability tending to one.

The paper lists 6b as an assumption of the T3 option. On a level-1 network it follows from condition 4, which the proof already needs
for Theorem 1 (`noAnomalousQuartets_iff_tQuartetNonanomalous`), so it does not appear here. See `consistencyT3_of_noAnomalous` for the
statement with 6b.

The proof is that of `consistency`, with `TINNiK.tests_correct_t3_of_t3Detectable` in place of `TINNiK.tests_correct`. -/
theorem consistencyT3 [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), TINNiK.IsT3MLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) :=
  consistencyT3_of_offModel hStd hLevel hNon
    (fun q hq hnt => QuartetTests.not_isT3Null_of_isNonCut (hBlob q hq hnt)) hX

/-- **The consistency claim of §4.3 with the T3 option, under conditions 5, 6a and 6b**, as the paper lists them for the FP edge detection
step. Condition 4, needed for Theorem 1, follows from 6b. -/
theorem consistencyT3_of_noAnomalous [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (h6b : TINNiK.NoAnomalousQuartets N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), TINNiK.IsT3MLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) :=
  consistencyT3 hStd hLevel (isTQuartetNonanomalous_of_noAnomalous hStd.phylogenetic h6b) hBlob hX

end TOBQMC
