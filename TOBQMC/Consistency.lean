module

public import TINNiK.Basic
public import TOBQMC.Level1
public import TOBQMC.WQC
public import Basic.Probability.Trinomial.Bridge

/-!
# TOB-QMC §4.3: statistical consistency for level-1 networks

The unnumbered claim at the end of §4.3 (`tob2025:consistency`), combining Theorem 1, Theorem 2 and
TINNiK Theorem 4: for level-1 networks, with levels `α_k → 0` and any `β > 0`, labelling the edges of
any optimal solution of Weighted Quartet Consensus by hypothesis tests on a disjoint cover and
contracting those labelled false positives returns the tree of blobs with probability tending to one.
The tests are TINNiK's star and cut tests; the T3 option is not treated.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The answer of Theorem 1 on counts `c`: every optimal solution of Weighted Quartet Consensus for `c`
is a refinement of the tree of blobs. -/
private def OptimaRefine {V E : Type*} (N : RootedNetwork V E X) (c : QuartetTree X → ℝ) : Prop :=
  ∀ B, IsBinaryTree B → (∀ T, IsBinaryTree T → quartetScore c T ≤ quartetScore c B) →
    treeOfBlobs N ⊆ B

/-- The counts of the first `k` terms of a sequence of gene trees. -/
private theorem geneCount_coords (k : ℕ) (ω : ℕ → Finset (Finset X)) :
    geneCount (fun i ω => ω i) k ω = quartetCount unroot (fun i : Fin k => ω i) := by
  funext s
  simp only [geneCount, quartetCount]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun i => if Displays (unroot (ω i)) s then 1 else 0)]

/-- The coordinates of the independent sequence of draws from the NMSC are a gene tree sample. -/
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

/-- **Theorem 1 for finite samples**: every optimal solution of Weighted Quartet Consensus on `k` independent
gene trees is a refinement of the tree of blobs, with probability tending to one. From
`theorem1_optimal` on the independent sequence, by continuity from below. -/
private theorem tendsto_optimaRefine {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}
    {θ : MetricData E} {ρ : ℝ} (hStd : StandardAssumptions N θ ρ)
    (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X)
    (hd : IsDist (geneTreeDist N θ ρ)) :
    Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
      OptimaRefine N (quartetCount unroot ω)) atTop (𝓝 1) := by
  let : MeasurableSpace (Finset (Finset X)) := ⊤
  have : MeasurableSingletonClass (Finset (Finset X)) := ⟨fun _ => trivial⟩
  set P := Trinomial.iidSeq (geneTreeDist N θ ρ) hd with hP
  have hae := theorem1_optimal hStd hEx hNon hX P (fun i ω => ω i) (isGeneTreeSample_iidSeq hd)
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

/-- **The consistency claim of §4.3** (`tob2025:consistency`), conditional on exchangeability. For a
binary level-1 network under the standard assumptions that is T-quartet-nonanomalous, at parameters
where CF-detectability holds, there are levels `α_k → 0` such that for any `β > 0`, any selection of
maximum likelihood topologies, any solver of Weighted Quartet Consensus and any selection of disjoint
covers, the method on `k` independent gene trees returns the tree of blobs with probability tending
to one.

The proof combines Theorem 1 (`theorem1_optimal`), Theorem 2 (`theorem2`) and TINNiK's Theorem 4, as the
paper says. The statement of TINNiK's Theorem 4 is about that algorithm's output; what the paper cites,
that the hypothesis tests return the correct answer on all four-taxon sets with probability going to one,
is established in its proof, and the Lean proof uses that step of the proof of
`TINNiK.theorem4_of_detectable`, as the lemma `TINNiK.tests_correct`. -/
theorem consistency [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hEx : External.AneEtAl2024.Exchangeability N θ ρ)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hdet : External.AllmanEtAl2023.CFDetectable N (nmscCF N θ ρ)) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmc ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  refine ⟨fun k => chiSqOneTail (Real.log k), QuartetTests.tendsto_chiSqOneTail_log,
    fun k => QuartetTests.chiSqOneTail_pos _, fun β hβ ml hml solve hsolve cover hcover => ?_⟩
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  have htests := TINNiK.tests_correct hN hX hStd.metric hStd.rho hdet
    (fun k => QuartetTests.chiSqOneTail_pos (Real.log k)) QuartetTests.tendsto_chiSqOneTail_log
    QuartetTests.tendsto_log_chiSqOneTail_log hβ hml
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd htests (tendsto_optimaRefine hStd hEx hNon hX hd))
  obtain ⟨⟨hB, -⟩, hopt⟩ := hω
  obtain ⟨hbin, hmax⟩ := hsolve (quartetCount unroot ω)
  have hTB := hopt _ hbin hmax
  have hcov := hcover _ hbin
  obtain ⟨H, hH, hHeq, -⟩ := id hbin
  rw [← theorem2 hN hStd.binary hLevel ⟨H, hH, hHeq⟩ hTB _ hcov, tobqmc]
  congr 1
  refine Finset.filter_congr fun A hA => ?_
  refine exists_congr fun Y => and_congr_right fun hY => ?_
  rw [hB]
  obtain ⟨s, -, rfl⟩ := (hcov A hA).around Y hY
  simp [QuartetTree.card_taxa]

end TOBQMC
