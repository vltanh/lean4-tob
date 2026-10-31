module

public import TOBQMC.BipartitionSearch
public import TOBQMC.ConsistencyT3

/-!
# TOB-QMC §4.3: the bipartition search combined with 3-fix-1-alter, with the T3 option

`TOBQMC/BipartitionSearch.lean` proves the claim of TOB-QMC at embedded lines 622-623 ("combining the bipartition
search heuristic with 3f1a yields a consistent method for level-1 networks") with TINNiK's star and cut tests. The T3
test is TOB-QMC's default option (`TOBQMC/ConsistencyT3.lean`). This file is the same claim with the T3 option, in the
same three forms as `TOBQMC/ConsistencyT3.lean`:

* `consistencyT3_search_of_offModel`: with what the T3 test uses on the non-treelike subsets, off the T3 model;
* `consistencyT3_search`: under conditions 4, 5 and 6a;
* `consistencyT3_search_of_noAnomalous`: under conditions 5, 6a and 6b, as the paper lists them.

The argument is that of the cut test. A true edge is not contracted, since all four-taxon subsets around its
bipartition are treelike and the tests are correct on all four-taxon subsets
(`TINNiK.tests_correct_t3_of_t3Detectable`). A false edge is contracted because of the disjoint cover, by Theorem 2.
Both are in `contractSides_cover_union_eq`, which does not depend on the test. The search itself, its counts
(`SearchOut.counts`) and its minimum (`pValue_lt_iff`) do not depend on the test either.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-- The p-value with which the tests of TINNiK's algorithm with the T3 option (`TINNiK.testedBT3`) judge a four-taxon
set: `0` when the star test does not reject at level `β`, and the p-value of the T3 test otherwise. Parallel to
`judgedP`. -/
def judgedPT3 (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β : ℝ) (c : QuartetTree X → ℝ)
    (Y : Finset X) : ℝ :=
  if β ≤ starPValue .lrt c Y then 0 else t3PValue c (ml c Y)

/-- The p-value is below `α` exactly when the tests judge the set non-treelike. -/
theorem judgedPT3_lt_iff {ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X} {α β : ℝ} {c : QuartetTree X → ℝ}
    {Y : Finset X} (hα : 0 < α) (hY : Y.card = 4) : judgedPT3 ml β c Y < α ↔ Y ∈ TINNiK.testedBT3 ml α β c := by
  simp only [judgedPT3, TINNiK.testedBT3, Set.mem_ofPred_eq, hY, true_and]
  by_cases h : β ≤ starPValue .lrt c Y
  · simp [h, hα]
  · simp [h]

/-- **The p-value of an edge with the T3 option**: the minimum of Algorithm 1's over the disjoint cover `Q` and of
Algorithm 2's. -/
def edgePT3 (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (β : ℝ) (c : QuartetTree X → ℝ)
    (Q : Finset (Finset X)) (o : SearchOut X) : ℝ :=
  min (minP (Q.val.map (judgedPT3 ml β c))) (o.pValue fun t => judgedPT3 ml β c t.taxa)

/-- The method with the T3 option and any further four-taxon sets `R` around the bipartitions. Parallel to
`tobqmcAround`. -/
def tobqmcAroundT3 (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (B : Finset (Finset X)) (Q R : Finset X → Finset (Finset X)) : Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A => ∃ Y ∈ Q A ∪ R A, Y ∈ TINNiK.testedBT3 ml α β c)

/-- **The combination of §4.3 with the T3 option**: from the tree `B`, contract the edges whose p-value `edgePT3`, the
minimum over the disjoint cover `Q` and over Algorithm 2 with limit `limit` and picks `pick`, is below `α`. Parallel
to `tobqmcSearch`. -/
def tobqmcSearchT3 (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (B : Finset (Finset X)) (Q : Finset X → Finset (Finset X))
    (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X) (limit : ℕ)
    (pick : Finset X → ℕ → SearchTuple X) : Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A =>
    edgePT3 ml β c (Q A) (bipartitionSearch A (fun t => judgedPT3 ml β c t.taxa)
      (argmin fun t => judgedPT3 ml β c t.taxa) limit (pick A)) < α)

/-- Consistency with the T3 option and with further four-taxon sets around the bipartitions, for any selection `R` of
them, possibly depending on the data, with the part of 6a that the T3 test uses. That the solution refines the tree of
blobs comes from `consistencyT3_of_offModel`, whose output is contained in the solution. Parallel to
`consistency_around`. -/
theorem consistencyT3_around_of_offModel [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
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
      ∀ (R : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ R c B A, Y.card = 4 ∧ (A ∩ Y).card = 2) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcAroundT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) (R (quartetCount unroot ω) (solve (quartetCount unroot ω))) =
              treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  have hdet := t3Detectable_of_level1 hStd hLevel hNon hOff
  obtain ⟨α, hα₀, hαpos, hrej⟩ := TINNiK.exists_levels_t3 hN hStd.metric hStd.rho hdet
  obtain ⟨α', -, -, hcons⟩ := consistencyT3_of_offModel hStd hLevel hNon hOff hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve cover hcover R hR => ?_⟩
  have htests := TINNiK.tests_correct_t3_of_t3Detectable hN hX hStd.metric hStd.rho hdet hα₀ hrej hβ hml
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun k ω hω => ?_)
    (TINNiK.tendsto_iidProb_and hd htests (hcons β hβ ml hml solve hsolve cover hcover))
  obtain ⟨⟨hB, -⟩, hout⟩ := hω
  obtain ⟨hbin, -⟩ := hsolve (quartetCount unroot ω)
  have hTB : treeOfBlobs N ⊆ solve (quartetCount unroot ω) := by
    rw [← hout]
    exact filter_subset _ _
  have hBu : IsUnrootedTree (solve (quartetCount unroot ω)) := by
    obtain ⟨H, hH, hu, -⟩ := hbin
    exact ⟨H, hH, hu⟩
  have hcov := hcover _ hbin
  have hRR := hR (quartetCount unroot ω) _ hbin
  rw [← contractSides_cover_union_eq hN hStd.binary hLevel hBu hTB _ _ hcov hRR, tobqmcAroundT3]
  congr 1
  refine Finset.filter_congr fun A hA => exists_congr fun Y => and_congr_right fun hY => ?_
  have hc : Y.card = 4 := by
    rcases mem_union.mp hY with hY | hY
    · obtain ⟨s, -, rfl⟩ := (hcov A hA).around Y hY
      exact QuartetTree.card_taxa s
    · exact (hRR A hA Y hY).1
  rw [hB]
  exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

/-- The claim of embedded lines 622-623 with the T3 option, with the part of 6a that the T3 test uses. Parallel to
`consistency_search`. -/
theorem consistencyT3_search_of_offModel [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
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
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcSearchT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) argmin limit
            (pick (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  obtain ⟨α, hα₀, hαpos, h⟩ := consistencyT3_around_of_offModel hStd hLevel hNon hOff hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve cover hcover argmin hargmin limit pick hpick => ?_⟩
  let R : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X) := fun c B A =>
    (bipartitionSearch A (fun t => judgedPT3 ml β c t.taxa) (argmin fun t => judgedPT3 ml β c t.taxa) limit
      (pick c B A)).testedSets
  have hR : ∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ R c B A, Y.card = 4 ∧ (A ∩ Y).card = 2 :=
    fun c B hB A hA Y hY => card_of_mem_testedSets (hargmin _) (hpick c B hB A hA) hY
  refine tendsto_iidProb_of_imp hd ?_ (h β hβ ml hml solve hsolve cover hcover R hR)
  filter_upwards [hα₀.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with k hk ω hω
  rw [← hω, tobqmcSearchT3, tobqmcAroundT3]
  congr 1
  refine Finset.filter_congr fun A hA => ?_
  rw [edgePT3, min_minP_pValue_lt_iff (hargmin _) hk.le]
  obtain ⟨hbin, -⟩ := hsolve (quartetCount unroot ω)
  refine exists_congr fun Y => and_congr_right fun hY => judgedPT3_lt_iff (hαpos k) ?_
  rcases mem_union.mp hY with hY | hY
  · obtain ⟨s, -, rfl⟩ := (hcover _ hbin A hA).around Y hY
    exact QuartetTree.card_taxa s
  · exact (hR _ _ hbin A hA Y hY).1

/-- **The claim of embedded lines 622-623 with the T3 option, under conditions 4, 5 and 6a.** Parallel to
`consistencyT3`: on a level-1 network condition 6b adds nothing to condition 4
(`noAnomalousQuartets_iff_tQuartetNonanomalous`). -/
theorem consistencyT3_search [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
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
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcSearchT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) argmin limit
            (pick (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) :=
  consistencyT3_search_of_offModel hStd hLevel hNon
    (fun q hq hnt => QuartetTests.not_isT3Null_of_isNonCut (hBlob q hq hnt)) hX

/-- **The claim of embedded lines 622-623 with the T3 option, under conditions 5, 6a and 6b**, as the paper lists them
for the T3 option. Condition 4, needed for Theorem 1, follows from 6b. Parallel to `consistencyT3_of_noAnomalous`. -/
theorem consistencyT3_search_of_noAnomalous [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
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
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcSearchT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (cover (solve (quartetCount unroot ω))) argmin limit
            (pick (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) :=
  consistencyT3_search hStd hLevel (isTQuartetNonanomalous_of_noAnomalous hStd.phylogenetic h6b) hBlob hX

/-- **The T3 option with 3f1a itself**, under conditions 5, 6a and 6b: the cover is the one of Algorithm 1, on the
blocks `P B A` of the quadripartition of the edge with side `A` of `B`, with anchors `z B A`. The number of four-taxon
subsets per edge is as for the cut test, at most `(n - 3) + 2 * limit + 2 * (n - 4)`
(`card_threeFixOneAlter_union_testedSets_le`). -/
theorem consistencyT3_threeFixOneAlter_search [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E}
    {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (h6b : TINNiK.NoAnomalousQuartets N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      External.AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), TINNiK.IsT3MLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (P : Finset (Finset X) → Finset X → Fin 4 → Finset X) (z : Finset (Finset X) → Finset X → Fin 4 → X),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B,
          (∀ i j, i ≠ j → Disjoint (P B A i) (P B A j)) ∧ univ.biUnion (P B A) = univ ∧
            P B A 0 ∪ P B A 1 = A ∧ (∀ i, P B A i ∈ B) ∧ ∀ i, z B A i ∈ P B A i) →
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcSearchT3 ml (α k) β (quartetCount unroot ω) (solve (quartetCount unroot ω))
            (fun A => threeFixOneAlter (P (solve (quartetCount unroot ω)) A) (z (solve (quartetCount unroot ω)) A))
            argmin limit (pick (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N)
          atTop (𝓝 1) := by
  obtain ⟨α, hα₀, hαpos, h⟩ := consistencyT3_search_of_noAnomalous hStd hLevel h6b hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve P z hPz argmin hargmin limit pick hpick => ?_⟩
  refine h β hβ ml hml solve hsolve (fun B A => threeFixOneAlter (P B A) (z B A)) (fun B hB A hA => ?_) argmin hargmin
    limit pick hpick
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hPz B hB A hA
  exact (threeFixOneAlter_isDisjointCover hB hA (P B A) h₁ h₂ h₃ h₄ (z B A) h₅).1

end TOBQMC
