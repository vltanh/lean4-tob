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

/-- **The consistency claim of §4.3** (`tob2025:consistency`). For a
binary level-1 network under the standard assumptions that is T-quartet-nonanomalous, whose non-treelike
4-taxon sets have distinct concordance factors (assumption 6a), there are levels `α_k → 0` such that for
any `β > 0`, any selection of maximum likelihood topologies, any solver of Weighted Quartet Consensus and
any selection of disjoint covers, the method on `k` independent gene trees returns the tree of blobs with
probability tending to one.

The proof combines Theorem 1 (`theorem1_optimal`), Theorem 2 (`theorem2`) and TINNiK's hypothesis tests, as
the paper says. The paper cites TINNiK's Theorem 4 for the tests' being correct on all four-taxon subsets. That is
a step of the proof of that theorem, not its statement (`TINNiK.tests_correct`), for generic parameters at `ρ = 0`.

Departure from the paper (E21 of the report): the argument here needs less than the citation. It uses correct
answers on the non-treelike subsets, by 6a (`TINNiK.tendsto_testedB`), and on the subsets the tree of blobs
resolves, by nonanomaly and exchangeability (`TINNiK.tendsto_not_testedB`, `NMSC.cut_alternatives`). A treelike
subset around a false positive is harmless, since the edge is labelled by another subset. This is not forced:
correctness on all subsets also holds under the printed assumptions, with a further fact on level-1 networks
that the argument here does not need. -/
theorem consistency [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
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
  -- the subsets that the tree of blobs resolves are not judged B-quartets
  have hres := tendsto_iidProb_forall hd (ι := {s : QuartetTree X // Displays (treeOfBlobs N) s})
    (fun s k ω => s.val.taxa ∉ testedB ml (chiSqOneTail (Real.log k)) β (quartetCount unroot ω))
    fun s => TINNiK.tendsto_not_testedB hN hStd.metric hStd.rho QuartetTests.tendsto_chiSqOneTail_log hβ hml
      ⟨fun r hr => (hNon s.val s.property r hr).ne,
        NMSC.cut_alternatives hN hStd.metric hStd.rho s.val
          (External.AllmanEtAl2023.inducedCutSplit_of_displays hN s.property)⟩
  -- the non-treelike subsets are, by 6a
  have hblob := tendsto_iidProb_forall hd
    (ι := {q : Finset X // q.card = 4 ∧ ¬ IsTreelike N q})
    (fun q k ω => q.val ∈ testedB ml (chiSqOneTail (Real.log k)) β (quartetCount unroot ω))
    fun q => TINNiK.tendsto_testedB hN hStd.metric hStd.rho
      (fun k => QuartetTests.chiSqOneTail_pos (Real.log k)) QuartetTests.tendsto_log_chiSqOneTail_log hβ hml
      q.property.1 (hBlob q.val q.property.1 q.property.2)
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd (TINNiK.tendsto_iidProb_and hd hres hblob)
      (tendsto_optimaRefine hStd hNon hX hd))
  obtain ⟨⟨hR, hB⟩, hopt⟩ := hω
  obtain ⟨hbin, hmax⟩ := hsolve (quartetCount unroot ω)
  have hTB := hopt _ hbin hmax
  have hcov := hcover _ hbin
  have hu := IsBinaryTree.isUnrootedTree hbin
  rw [← theorem2 hN hStd.binary hLevel hu hTB _ hcov, tobqmc]
  congr 1
  refine Finset.filter_congr fun A hA => ?_
  by_cases hAT : A ∈ treeOfBlobs N
  · -- a true positive: no subset around it is judged a B-quartet, and all are treelike
    constructor
    · rintro ⟨Y, hYQ, hY⟩
      obtain ⟨s, hs, rfl⟩ := (hcov A hA).around Y hYQ
      have hbi := (mem_filter.mp (mem_filter.mp hs).1).2
      exact absurd hY (hR ⟨s, ⟨A, hAT, hbi⟩⟩)
    · rintro ⟨Y, hYQ, hnt⟩
      obtain ⟨s, hs, rfl⟩ := (hcov A hA).around Y hYQ
      have hbi := (mem_filter.mp (mem_filter.mp hs).1).2
      exact absurd (Level1.isTreelike_of_hasCutSplit hN (mem_filter.mp hAT).2.2.2 (QuartetTree.card_taxa s)
        (s.2.2.1 _ hbi)) hnt
  · -- a false positive: Lemma 4 finds a non-treelike subset in the cover, and it is judged a B-quartet
    obtain ⟨Y, hYQ, hnt⟩ := Level1.exists_not_isTreelike hN hStd.binary hLevel hu hTB hA hAT (hcov A hA)
    obtain ⟨s, -, rfl⟩ := (hcov A hA).around Y hYQ
    exact ⟨fun _ => ⟨_, hYQ, hnt⟩, fun _ =>
      ⟨_, hYQ, hB ⟨s.taxa, QuartetTree.card_taxa s, hnt⟩⟩⟩

end TOBQMC
