module

public import Basic.Defs
public import Basic.Testing.Defs
public import Basic.Testing.IID
public import Basic.Testing.MissingTaxa
public import Basic.Testing.Trinomial.Whiten
public import External.MitchellAllmanRhodes2019.CutModel
public import External.MitchellAllmanRhodes2019.T1Limit
public import External.MitchellAllmanRhodes2019.T3Density
public import External.MitchellAllmanRhodes2019.T3Limit
public import External.MitchellAllmanRhodes2019.T3Test
public import External.StudierKeppler1988.Lemma
public import Phylogenetics.Hierarchy.Defs
public import Phylogenetics.NMSC.Defs
public import Phylogenetics.Network.Defs
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Tree.Defs
public import Phylogenetics.Tree.Metric
public import TINNiK.Basic
public import TINNiK.MissingTaxa
public import TINNiK.Statistics.Definitions
public import TINNiK.Statistics.OpenCutModel

/-!
# The main results of TINNiK

Allman, Baños, Mitchell, Rhodes, Algorithms Mol. Biol. 19, 2024: Theorem 4, what the paper says in passing, and the main results of Mitchell, Allman, Rhodes 2019 (`mitchell_`), whose tests it uses, and of Studier, Keppler 1988 (`studierKeppler_`), on its neighbor joining.

Each theorem is stated in plain terms and proved from the libraries. `papers/TINNiK/README.md` and `papers/TINNiK/REPORT.md` describe the formalization and list every correction and departure, and `papers/TINNiK/palomar/` has the paper's entry for Palomar. `MainResults` imports this module with those of the other papers.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

namespace TreeOfBlobs

universe u

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC Filter Topology

/-- **TINNiK, Theorem 4.** For generic numerical parameters on a binary network, there is a sequence `α_m → 0` such that for
any `β > 0` and `0 ≤ δ < 2`, any exact tree builder and any selection of maximum likelihood topologies, the TINNiK
algorithm on `m` independent gene trees infers the tree of blobs with probability tending to one. -/
theorem theorem4 {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
    {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hX : 4 ≤ Fintype.card X) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 →
          ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCount unroot ω) = treeOfBlobs N) atTop (𝓝 1) := TINNiK.theorem4 hN hX hBin

end

/-! ## What the paper says in passing, and its other claims -/

section

open Phylogenetics Phylogenetics.RootedNetwork ECToBlob TOBQMC AllmanEtAl2023 Filter Topology

/-- **TINNiK, the sentence before Theorem 4: with missing taxa.** As `theorem4`, for gene trees on subsets of the taxa that leave each set of four taxa on more and more of them. -/
theorem tinnik_theorem4_missing {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hX : 4 ≤ Fintype.card X) (hBin : N.IsBinary) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → ∀ on : (m : ℕ) → Fin m → Finset X, TINNiK.Covers on →
        ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧
          ∀ (β δ : ℝ), 0 < β → 0 ≤ δ → δ < 2 → ∀ (M : TreeBuilder X), IsExactBuilder M →
          ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
            Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
              tinnik ml (α m) β δ M (quartetCountOn unroot (on m) ω) = treeOfBlobs N) atTop (𝓝 1) :=
  TINNiK.theorem4_missing hN hX hBin

/-- **TINNiK, Appendix C.1: no maximum on the open cut model** (E31 of the report). At the counts `n > 0` in one coordinate, for example `(1, 0, 0)`, no point of the cut model of Definition 7 maximizes the trinomial likelihood. Not every count with a zero fails. -/
theorem tinnik_not_exists_generatingCutModel_maximizer (i : Fin 3) {n : ℕ} (hn : 0 < n) :
    ¬ ∃ p, TINNiK.GeneratingCutModel p ∧ ∀ q, TINNiK.GeneratingCutModel q →
      TINNiK.likelihood (TINNiK.concentratedCounts i n) q ≤ TINNiK.likelihood (TINNiK.concentratedCounts i n) p :=
  TINNiK.not_exists_generatingCutModel_maximizer i hn

end

/-! ## The sources that it cites -/

section

open Phylogenetics Phylogenetics.RootedNetwork Filter Topology Finset MeasureTheory ProbabilityTheory

open External.MitchellAllmanRhodes2019 Trinomial QuartetTests in
/-- **Mitchell, Allman, Rhodes 2019, Proposition 4.1**, for the trinomial. At the true point `(1 - 2φ/3, φ/3, φ/3)`, `0 < φ ≤ 1`, the likelihood ratio statistic of model T3 and the variable `t3Var φ`, with `Z ~ N(0, 1)`, `Z̄ ~ N(μ₀(n), 1)` independent, converge in
distribution to the same limit. The source's route through van der Vaart's Theorem 16.7 is replaced by the central limit theorem for this model. -/
theorem mitchell_proposition4_1 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≤ 1) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ t3S (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map (t3Var φ)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) :=
  proposition4_1 hφ hφ1

/-- **Mitchell, Allman, Rhodes 2019, Proposition 4.2.** The printed density `t3Density` is the density of the variable `t3Var φ`, for all `φ < 3/2`; the source states it for `(0, 1]`. -/
theorem mitchell_proposition4_2 {φ : ℝ} (hφ : φ < 3 / 2) (n : ℝ) :
    (∀ lam, 0 ≤ t3Density φ n lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).map (t3Var φ) =
        volume.withDensity (fun lam => ENNReal.ofReal (t3Density φ n lam)) :=
  External.MitchellAllmanRhodes2019.proposition4_2 hφ n

open External.MitchellAllmanRhodes2019 Trinomial QuartetTests in
/-- **Mitchell, Allman, Rhodes 2019, Proposition 5.1**, for the trinomial: as `mitchell_proposition4_1`, for model T1 and the variable `t1Var`. -/
theorem mitchell_proposition5_1 {φ : ℝ} (hφ : 0 < φ ∧ φ < 3 / 2) (hφ1 : φ ≤ 1) : ∃ ν : ProbabilityMeasure ℝ,
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((Measure.pi fun _ : Fin n ↦
          (cutPoint_isDist hφ).toPMF.toMeasure).map fun η ↦ t1S (count η 0) (count η 1) (count η 2)))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) ∧
    (∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ ↦ ∫ x, f x ∂((normalSample (muZero φ n)).map t1Var))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure ℝ)))) :=
  proposition5_1 hφ hφ1

/-- **Mitchell, Allman, Rhodes 2019, Proposition 5.2.** The printed density `t1Density` is the density of the variable `t1Var`, with `μ₀ = muZero φ n`. -/
theorem mitchell_proposition5_2 (φ n : ℝ) :
    (∀ lam, 0 ≤ t1Density (muZero φ n) lam) ∧
      ((gaussianReal 0 1).prod (gaussianReal (muZero φ n) 1)).map t1Var =
        volume.withDensity (fun lam => ENNReal.ofReal (t1Density (muZero φ n) lam)) :=
  External.MitchellAllmanRhodes2019.proposition5_2 φ n

/-- **Studier, Keppler 1988, the Lemma fails at a polytomy.** "If `i` and `j` are neighbors, then `S_ij` is the strictly least element in its row and column" fails on the star with four leaves and unit weights, where all the `S_ij` are equal. The letter asks for positive branches and doesn't define "neighbors", read here as a cherry of a resolution. If it means binary trees, this is a failure of wording. Its Theorem holds on such trees. -/
theorem studierKeppler_not_lemmaAsPrinted : ¬ External.StudierKeppler1988.LemmaAsPrinted := External.StudierKeppler1988.not_lemmaAsPrinted

end

end TreeOfBlobs
