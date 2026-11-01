module

public import Basic.Testing.Tails
public import TOBQMC.BipartitionSearch
public import TOBQMC.ConsistencyT3

/-!
# TOB-QMC: the implementation of the tests, with the star test on the minimizer only

`TOBQMC.tobqmc` and `TOBQMC.tobqmcSearch` read "TINNiK's hypothesis tests" as TINNiK's Step 2 on each four-taxon subset tested.
TOB-QMC's implementation (v5, embedded lines 127-140) is different:

> TOB-QMC-exhaustive tests for treelikeness among all four-taxon subsets around each edge in the refinement tree, storing the
> minimum p-value found and the minimizer four-taxon subset. [...] After performing the search around each edge, edges are
> contracted if the null hypothesis of the treelikeness test is rejected (i.e., `pmin < α`). However, the treelikeness test cannot
> be used when the evolutionary relationship among the four species is a polytomy [...]. To rule out this scenario, TINNiK's star
> test is applied to the minimizer four-taxon subset, and if the null hypothesis is not rejected (i.e., `pmin ≥ β`), the edge is
> contracted. Thus, higher `α` and lower `β` result in more edges being contracted. [...] by storing minimum p-values found and
> taxon minimizers for each edge, the impact of `α`, `β` can be evaluated offline.

The second `pmin` is the p-value of the star test on the minimizer, as the sentence before it says; the printed name is a slip.

`tobqmcImplementation` is this procedure, for the p-value `P` of a treelikeness test, on any selection of subsets tested around
each edge. The claim made for the procedure is the paper's consistency claim for level-1 networks (embedded lines 597-600, 622-623):
it holds. `consistency_implementation` is the claim with the cut test and `consistencyT3_implementation` with the T3 test, the
paper's default, for any selection of tested subsets containing a disjoint cover and lying around the edge, any minimizers, and any
`β > 0`. So the star test on the minimizer does no harm: the star test plays no part in the limit under these assumptions, since a
false edge has a non-treelike subset in the cover, whose treelikeness p-value is below `α` by condition 6a, and on a true edge
every subset tested is treelike, and off the centroid.

* `tobqmcImplementation_eq_of_tests`: the deterministic step, from Theorem 2.
* `consistency_implementation_exhaustive`, `consistency_implementation_threeFixOneAlter`,
  `consistency_implementation_search`: TOB-QMC-exhaustive, TOB-QMC-3f1a and the combination of Algorithm 2 with 3f1a, as instances.
  The modes `fast` and `default`, which use Algorithm 2 alone, have no consistency claim in the paper.
* `tobqmc_subset_implementation`: this contracts fewer edges than the reading of `TOBQMC.tobqmc`, which applies the star test to all
  subsets tested.
* `implementation_contracted_mono`, `implementation_mono`: "higher `α` and lower `β` result in more edges being contracted".
* `tobqmcImplementation_eq_offline`: "the impact of `α`, `β` can be evaluated offline".
* `starPValue_eq_one_of_forall_eq`, `starPValue_lt_one`: the claim at embedded lines 171-172, "setting `β = 1` ensures the null of the
  star test is always rejected", holds exactly when the three counts are not all equal.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace TOBQMC

variable {V E X : Type*} [Fintype X] [DecidableEq X]

/-! ### The procedure -/

/-- `Y` is a minimizer four-taxon subset of the p-value `P` among the subsets `R` tested. Ties are not resolved by the paper, and the
results hold for every selection. -/
def IsMinimizerOf (P : Finset X → ℝ) (R : Finset (Finset X)) (Y : Finset X) : Prop :=
  Y ∈ R ∧ ∀ Y' ∈ R, P Y ≤ P Y'

/-- What is stored for an edge (embedded lines 128-129, 139): the minimum p-value found and the minimizer four-taxon subset. -/
structure EdgeRecord (X : Type*) where
  pmin : ℝ
  minimizer : Finset X

/-- The record of the search around an edge: the minimum `pmin`, starting from `1` as in Algorithm 1 of the supplement, of the p-values
of the subsets `R` tested, with the minimizer `Y`. -/
def edgeRecord (P : Finset X → ℝ) (R : Finset (Finset X)) (Y : Finset X) : EdgeRecord X :=
  ⟨minP (R.val.map P), Y⟩

/-- The decision from what is stored, with the p-value `star` of the star test (embedded lines 133-137): contract when `pmin < α`, or
when the star test does not reject on the minimizer at level `β`. -/
def EdgeRecord.Contracted (star : Finset X → ℝ) (α β : ℝ) (r : EdgeRecord X) : Prop :=
  r.pmin < α ∨ β ≤ star r.minimizer

/-- The evaluation offline: from the tree `B` and the records of its edges, contract the edges decided by `α`, `β`. -/
def tobqmcOffline (star : Finset X → ℝ) (α β : ℝ) (B : Finset (Finset X)) (rec : Finset X → EdgeRecord X) :
    Finset (Finset X) :=
  contractSides B ((internalSides B).filter fun A => (rec A).Contracted star α β)

/-- **The implementation at embedded lines 133-137** (`tob2025:implementation`): from the tree `B`, with `tested A` the four-taxon subsets
tested around the edge with side `A`, and `mini A` the minimizer, contract the edge when `pmin < α` or when the star test on `mini A` does
not reject at level `β`. `P` is the p-value of the treelikeness test. -/
def tobqmcImplementation (P star : Finset X → ℝ) (α β : ℝ) (B : Finset (Finset X))
    (tested : Finset X → Finset (Finset X)) (mini : Finset X → Finset X) : Finset (Finset X) :=
  tobqmcOffline star α β B fun A => edgeRecord P (tested A) (mini A)

/-- **"The impact of `α`, `β` can be evaluated offline, avoiding full re-computation of the TOB"** (embedded lines 139-140): the output
is a function of `α`, `β` and of what is stored for each edge, which does not depend on `α`, `β`. -/
theorem tobqmcImplementation_eq_offline (P star : Finset X → ℝ) (α β : ℝ) (B : Finset (Finset X))
    (tested : Finset X → Finset (Finset X)) (mini : Finset X → Finset X) :
    tobqmcImplementation P star α β B tested mini =
      tobqmcOffline star α β B fun A => edgeRecord P (tested A) (mini A) := rfl

omit [Fintype X] [DecidableEq X] in
/-- The edges contracted are monotone in `α`, and antitone in `β`. -/
theorem implementation_contracted_mono {star : Finset X → ℝ} {α α' β β' : ℝ} (hα : α ≤ α') (hβ : β' ≤ β)
    {r : EdgeRecord X} (h : r.Contracted star α β) : r.Contracted star α' β' :=
  h.imp (fun h => h.trans_le hα) (fun h => hβ.trans h)

/-- **"Thus, higher `α` and lower `β` result in more edges being contracted"** (embedded lines 137-138): the output is antitone in `α`,
and monotone in `β`, as a family of splits. -/
theorem implementation_mono (P star : Finset X → ℝ) {α α' β β' : ℝ} (hα : α ≤ α') (hβ : β' ≤ β)
    (B : Finset (Finset X)) (tested : Finset X → Finset (Finset X)) (mini : Finset X → Finset X) :
    tobqmcImplementation P star α' β' B tested mini ⊆ tobqmcImplementation P star α β B tested mini := by
  intro A hA
  simp only [tobqmcImplementation, tobqmcOffline, contractSides, mem_filter] at hA ⊢
  obtain ⟨hAB, h₁, h₂⟩ := hA
  exact ⟨hAB, fun h => h₁ ⟨h.1, implementation_contracted_mono hα hβ h.2⟩,
    fun h => h₂ ⟨h.1, implementation_contracted_mono hα hβ h.2⟩⟩

/-- **The implementation contracts fewer edges than the reading of `tobqmc`**, at levels `α ≤ 1`. An edge that it contracts has a subset
tested that TINNiK's Step 2 judges non-treelike, as `tobqmc` asks, with the star test on all subsets tested. The difference: a subset other
than the minimizer on which the star test does not reject contracts the edge in `tobqmc`, and not here. -/
theorem tobqmc_subset_implementation (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) {α β : ℝ} (hα : α ≤ 1)
    (c : QuartetTree X → ℝ) (B : Finset (Finset X)) {tested : Finset X → Finset (Finset X)}
    {mini : Finset X → Finset X} (hfour : ∀ A ∈ internalSides B, ∀ Y ∈ tested A, Y.card = 4)
    (hmini : ∀ A ∈ internalSides B, mini A ∈ tested A) :
    tobqmc ml α β c B tested ⊆
      tobqmcImplementation (fun Y => cutPValue c (ml c Y)) (starPValue .lrt c) α β B tested mini := by
  have key : ∀ A, A ∈ internalSides B →
      (edgeRecord (fun Y => cutPValue c (ml c Y)) (tested A) (mini A)).Contracted (starPValue .lrt c) α β →
        ∃ Y ∈ tested A, Y ∈ testedB ml α β c := by
    rintro A hA (h | h)
    · obtain ⟨x, hx, hxα⟩ := (minP_lt_iff hα).1 h
      obtain ⟨Y, hY, rfl⟩ := Multiset.mem_map.1 hx
      exact ⟨Y, mem_def.2 hY, hfour A hA Y (mem_def.2 hY), Or.inr hxα⟩
    · exact ⟨mini A, hmini A hA, hfour A hA _ (hmini A hA), Or.inl h⟩
  intro A hA
  simp only [tobqmc, tobqmcImplementation, tobqmcOffline, contractSides, mem_filter] at hA ⊢
  obtain ⟨hAB, h₁, h₂⟩ := hA
  exact ⟨hAB, fun h => h₁ ⟨h.1, key A h.1 h.2⟩, fun h => h₂ ⟨h.1, key _ h.1 h.2⟩⟩

/-! ### The deterministic step -/

/-- **The implementation returns the tree of blobs when the tests are right**, on a refinement `B` of the tree of blobs of a binary level-1
network. The subsets tested around an edge contain a disjoint cover `Q`, and lie around the edge. The tests are right if the treelikeness
test does not reject on a treelike subset, and rejects on the others, and the star test rejects on the treelike subsets. The star test on
a non-treelike subset does not matter. A false positive is contracted because of `Q`, by Theorem 2: its `pmin` is below `α`. On a true edge,
by Lemma 2, all the subsets tested are treelike, the minimizer among them. -/
theorem tobqmcImplementation_eq_of_tests [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hBin : N.IsBinary) (hLevel : IsLevelOne N) {B : Finset (Finset X)} (hB : IsUnrootedTree B)
    (hTB : treeOfBlobs N ⊆ B) {tested : Finset X → Finset (Finset X)} {mini : Finset X → Finset X}
    (hcover : ∀ A ∈ internalSides B, ∃ Q ⊆ tested A, IsDisjointCover B A Q)
    (haround : ∀ A ∈ internalSides B, ∀ Y ∈ tested A, Y.card = 4 ∧ (A ∩ Y).card = 2)
    (hmini : ∀ A ∈ internalSides B, mini A ∈ tested A)
    {P star : Finset X → ℝ} {α β : ℝ} (hα : α ≤ 1)
    (htree : ∀ Y : Finset X, Y.card = 4 → IsTreelike N Y → α ≤ P Y ∧ star Y < β)
    (hnon : ∀ Y : Finset X, Y.card = 4 → ¬ IsTreelike N Y → P Y < α) :
    tobqmcImplementation P star α β B tested mini = treeOfBlobs N := by
  have htrue : ∀ A ∈ treeOfBlobs N, A ∉ (internalSides B).filter fun A =>
      (edgeRecord P (tested A) (mini A)).Contracted star α β := by
    intro A hAT hC
    obtain ⟨hint, hor⟩ := mem_filter.mp hC
    have hcut := (mem_filter.mp hAT).2.2.2
    have htl : ∀ Y ∈ tested A, IsTreelike N Y := fun Y hY =>
      Level1.isTreelike_of_hasCutSplit hN hcut (haround A hint Y hY).1 (haround A hint Y hY).2
    rcases hor with h | h
    · obtain ⟨x, hx, hxα⟩ := (minP_lt_iff hα).1 h
      obtain ⟨Y, hY, rfl⟩ := Multiset.mem_map.1 hx
      have hY' := mem_def.2 hY
      exact absurd hxα (not_lt.2 (htree Y (haround A hint Y hY').1 (htl Y hY')).1)
    · have hY := hmini A hint
      exact absurd h (not_le.2 (htree _ (haround A hint _ hY).1 (htl _ hY)).2)
  have hfalse : ∀ A ∈ internalSides B, ∀ Y ∈ tested A, ¬ IsTreelike N Y →
      (edgeRecord P (tested A) (mini A)).Contracted star α β := fun A hA Y hY hnt =>
    Or.inl ((minP_lt_iff hα).2 ⟨P Y, Multiset.mem_map.2 ⟨Y, mem_def.1 hY, rfl⟩, hnon Y (haround A hA Y hY).1 hnt⟩)
  choose! Q hQsub hQ using hcover
  have h2 := theorem2 hN hBin hLevel hB hTB Q hQ
  ext A
  rw [← h2]
  simp only [tobqmcImplementation, tobqmcOffline, contractSides, mem_filter]
  constructor
  · rintro ⟨hAB, h₁, h₂⟩
    refine ⟨hAB, ?_, ?_⟩
    · rintro ⟨hint, Y, hY, hnt⟩
      exact h₁ ⟨hint, hfalse A hint Y (hQsub A hint hY) hnt⟩
    · rintro ⟨hint, Y, hY, hnt⟩
      exact h₂ ⟨hint, hfalse _ hint Y (hQsub _ hint hY) hnt⟩
  · intro h
    have hAT : A ∈ treeOfBlobs N := by
      rw [← h2]
      simp only [contractSides, mem_filter]
      exact h
    refine ⟨h.1, fun hC => htrue A hAT (mem_filter.2 hC), fun hC => htrue _ (Level1.mem_treeOfBlobs_compl hAT) (mem_filter.2 hC)⟩

/-! ### Consistency -/

/-- **The claim of TOB-QMC for its implementation**, with the cut test (`tob2025:implementation`): under the hypotheses of
`TOBQMC.consistency`, there are levels `α_k → 0` such that for any `β > 0`, any selection of maximum likelihood topologies, any solver of
Weighted Quartet Consensus, any selection `tested` of four-taxon subsets around each edge that contains a disjoint cover, possibly depending
on the data, and any minimizers, the procedure with the star test on the minimizer returns the tree of blobs with probability tending
to one.

The levels are those of `TOBQMC.consistency`. On the event that the tests are correct on all four-taxon subsets (`TINNiK.tests_correct`), and
that the solution refines the tree of blobs, which `TOBQMC.consistency` gives, the cut test rejects on the non-treelike subsets
(`TINNiK.Rejects`), and it does not reject on the treelike ones, on which the star test rejects. Then
`tobqmcImplementation_eq_of_tests` applies. -/
theorem consistency_implementation [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (tested : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∃ Q ⊆ tested c B A, IsDisjointCover B A Q) →
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ tested c B A, Y.card = 4 ∧ (A ∩ Y).card = 2) →
      ∀ (mini : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B,
          IsMinimizerOf (fun Y => cutPValue c (ml c Y)) (tested c B A) (mini c B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcImplementation (fun Y => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) Y))
            (starPValue .lrt (quartetCount unroot ω)) (α k) β (solve (quartetCount unroot ω))
            (tested (quartetCount unroot ω) (solve (quartetCount unroot ω)))
            (mini (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  have hdet := Level1.cfDetectable hStd hLevel hNon hBlob
  obtain ⟨α, hα₀, hαpos, hrej⟩ := TINNiK.exists_levels hN hStd.metric hStd.rho hdet
  obtain ⟨α', -, -, hcons⟩ := consistency hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve tested hcover haround mini hmini => ?_⟩
  have htests := TINNiK.tests_correct hN hX hStd.metric hStd.rho hdet hα₀ hrej hβ hml
  -- the cut test rejects on the non-treelike subsets
  have hall := tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4 ∧ ¬ IsTreelike N q})
    (fun q k ω => ∀ s ∈ treesOn q.val, cutPValue (quartetCount unroot ω) s < α k)
    (fun q => hrej q.val q.property.1 q.property.2)
  -- a disjoint cover, to use `TOBQMC.consistency` for the refinement
  choose! Q₀ hQ₀ using fun (B : Finset (Finset X)) (hB : IsBinaryTree B) (A : Finset X) (hA : A ∈ internalSides B) =>
    hcover (fun _ => 0) B hB A hA
  have hrefine := hcons β hβ ml hml solve hsolve Q₀ fun B hB A hA => (hQ₀ B hB A hA).2
  refine tendsto_iidProb_of_imp hd ?_
    (TINNiK.tendsto_iidProb_and hd htests (TINNiK.tendsto_iidProb_and hd hall hrefine))
  filter_upwards [hα₀.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with k hk ω hω
  obtain ⟨⟨hBq, -⟩, hnt, hout⟩ := hω
  obtain ⟨hbin, -⟩ := hsolve (quartetCount unroot ω)
  have hTB : treeOfBlobs N ⊆ solve (quartetCount unroot ω) := by
    rw [← hout]
    exact filter_subset _ _
  refine tobqmcImplementation_eq_of_tests hN hStd.binary hLevel (IsBinaryTree.isUnrootedTree hbin) hTB
    (hcover _ _ hbin) (haround _ _ hbin) (fun A hA => (hmini _ _ hbin A hA).1) hk.le ?_ ?_
  · intro Y hY htl
    have hnotB : Y ∉ testedB ml (α k) β (quartetCount unroot ω) := by
      rw [hBq]
      exact fun h => h.2 htl
    simp only [testedB, Set.mem_ofPred_eq, hY, true_and, not_or, not_le, not_lt] at hnotB
    exact ⟨hnotB.2, hnotB.1⟩
  · intro Y hY hnty
    exact hnt ⟨Y, hY, hnty⟩ _ (hml _ Y hY).1

/-- **The claim of TOB-QMC for its implementation, with the T3 test**, the paper's default (`tob2025:implementation`), under conditions 4, 5
and 6a. Parallel to `consistency_implementation`, through `TINNiK.tests_correct_t3_of_t3Detectable`. On a level-1 network 6b follows from
condition 4 (`noAnomalousQuartets_iff_tQuartetNonanomalous`). -/
theorem consistencyT3_implementation [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), TINNiK.IsT3MLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (tested : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∃ Q ⊆ tested c B A, IsDisjointCover B A Q) →
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ Y ∈ tested c B A, Y.card = 4 ∧ (A ∩ Y).card = 2) →
      ∀ (mini : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B,
          IsMinimizerOf (fun Y => t3PValue c (ml c Y)) (tested c B A) (mini c B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcImplementation (fun Y => t3PValue (quartetCount unroot ω) (ml (quartetCount unroot ω) Y))
            (starPValue .lrt (quartetCount unroot ω)) (α k) β (solve (quartetCount unroot ω))
            (tested (quartetCount unroot ω) (solve (quartetCount unroot ω)))
            (mini (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  have hN := hStd.phylogenetic
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hd : IsDist (geneTreeDist N θ ρ) :=
    ⟨geneTreeDist_nonneg hN hStd.metric hStd.rho, sum_geneTreeDist hN hStd.metric hStd.rho⟩
  have hOff : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q → ¬ IsT3Null (nmscCF N θ ρ) q :=
    fun q hq hnt => QuartetTests.not_isT3Null_of_isNonCut (hBlob q hq hnt)
  have hdet := t3Detectable_of_level1 hStd hLevel hNon hOff
  obtain ⟨α, hα₀, hαpos, hrej⟩ := TINNiK.exists_levels_t3 hN hStd.metric hStd.rho hdet
  obtain ⟨α', -, -, hcons⟩ := consistencyT3 hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve tested hcover haround mini hmini => ?_⟩
  have htests := TINNiK.tests_correct_t3_of_t3Detectable hN hX hStd.metric hStd.rho hdet hα₀ hrej hβ hml
  have hall := tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4 ∧ ¬ IsTreelike N q})
    (fun q k ω => ∀ s ∈ treesOn q.val, t3PValue (quartetCount unroot ω) s < α k)
    (fun q => hrej q.val q.property.1 q.property.2)
  choose! Q₀ hQ₀ using fun (B : Finset (Finset X)) (hB : IsBinaryTree B) (A : Finset X) (hA : A ∈ internalSides B) =>
    hcover (fun _ => 0) B hB A hA
  have hrefine := hcons β hβ ml hml solve hsolve Q₀ fun B hB A hA => (hQ₀ B hB A hA).2
  refine tendsto_iidProb_of_imp hd ?_
    (TINNiK.tendsto_iidProb_and hd htests (TINNiK.tendsto_iidProb_and hd hall hrefine))
  filter_upwards [hα₀.eventually (gt_mem_nhds (zero_lt_one' ℝ))] with k hk ω hω
  obtain ⟨⟨hBq, -⟩, hnt, hout⟩ := hω
  obtain ⟨hbin, -⟩ := hsolve (quartetCount unroot ω)
  have hTB : treeOfBlobs N ⊆ solve (quartetCount unroot ω) := by
    rw [← hout]
    exact filter_subset _ _
  refine tobqmcImplementation_eq_of_tests hN hStd.binary hLevel (IsBinaryTree.isUnrootedTree hbin) hTB
    (hcover _ _ hbin) (haround _ _ hbin) (fun A hA => (hmini _ _ hbin A hA).1) hk.le ?_ ?_
  · intro Y hY htl
    have hnotB : Y ∉ TINNiK.testedBT3 ml (α k) β (quartetCount unroot ω) := by
      rw [hBq]
      exact fun h => h.2 htl
    simp only [TINNiK.testedBT3, Set.mem_ofPred_eq, hY, true_and, not_or, not_le, not_lt] at hnotB
    exact ⟨hnotB.2, hnotB.1⟩
  · intro Y hY hnty
    exact hnt ⟨Y, hY, hnty⟩ _ (hml _ Y hY).1

/-- **The blocks at a side of an edge of a binary tree**: a side `S` with at least two taxa is the disjoint union of two sides of the tree.
Rooting the tree, either `S` is a cluster, and these are its two children, or its complement is a cluster with parent `R` and other child
`D`, and these are `Rᶜ` and `D`. -/
theorem exists_blocks_of_isBinaryTree {T : Finset (Finset X)} (hT : IsBinaryTree T) {S : Finset X} (hS : S ∈ T)
    (h2 : 2 ≤ S.card) : ∃ P₀ ∈ T, ∃ P₁ ∈ T, Disjoint P₀ P₁ ∧ P₀ ∪ P₁ = S := by
  obtain ⟨H, hH, rfl, hbin⟩ := hT
  have hchild : ∀ {R : Finset X}, R ∈ H → 2 ≤ R.card →
      ∃ C D, C ∈ childClusters H R ∧ D ∈ childClusters H R ∧ Disjoint C D ∧ C ∪ D = R ∧ childClusters H R = {C, D} := by
    intro R hR hR2
    obtain ⟨C, D, hne, hCD⟩ := card_eq_two.mp (hbin R hR hR2)
    have hC : C ∈ childClusters H R := hCD ▸ mem_insert_self _ _
    have hD : D ∈ childClusters H R := hCD ▸ mem_insert_of_mem (mem_singleton_self _)
    have hsup := hH.sup_childClusters hR2
    rw [hCD] at hsup
    simp only [sup_insert, sup_singleton, id, sup_eq_union] at hsup
    exact ⟨C, D, hC, hD, hH.disjoint_of_mem_childClusters hC hD hne, hsup, hCD⟩
  have hsideOf : ∀ {C R : Finset X}, C ∈ childClusters H R → C ∈ unroot H := fun {C R} hC => by
    obtain ⟨hCH, hCR, -⟩ := mem_childClusters.mp hC
    exact mem_unroot.2 (Or.inl ⟨hCH, fun h => by
      subst h
      exact hCR.2 (subset_univ _)⟩)
  by_cases hSH : S ∈ H
  · obtain ⟨C, D, hC, hD, hdis, hun, -⟩ := hchild hSH h2
    exact ⟨C, hsideOf hC, D, hsideOf hD, hdis, hun⟩
  · obtain ⟨hcH, hcu⟩ : Sᶜ ∈ H ∧ Sᶜ ≠ univ := by
      rcases mem_unroot.1 hS with h | h
      · exact absurd h.1 hSH
      · exact h
    set R := parentCluster H Sᶜ with hRdef
    have hRH : R ∈ H := hH.parentCluster_mem hcH hcu
    have hcR : Sᶜ ⊂ R := hH.ssubset_parentCluster hcH hcu
    have hcchild : Sᶜ ∈ childClusters H R := hH.mem_childClusters_parentCluster hcH hcu
    have hR2 : 2 ≤ R.card := by
      have hne := hH.2.2.1 _ hcH
      have := card_lt_card hcR
      have := card_pos.2 hne
      omega
    obtain ⟨C, D, hC, hD, hdis, hun, hCD⟩ := hchild hRH hR2
    -- the other child
    obtain ⟨D', hD', hdis', hun'⟩ : ∃ D', D' ∈ childClusters H R ∧ Disjoint Sᶜ D' ∧ Sᶜ ∪ D' = R := by
      rw [hCD] at hcchild
      rcases mem_insert.1 hcchild with h | h
      · exact ⟨D, hD, h ▸ hdis, h ▸ hun⟩
      · rw [mem_singleton.1 h]
        exact ⟨C, hC, hdis.symm, by rw [union_comm]; exact hun⟩
    have hRu : R ≠ univ := by
      intro hRu
      refine hSH ?_
      have : D' = S := by
        ext x
        have hx : x ∈ Sᶜ ∪ D' := hun' ▸ hRu ▸ mem_univ x
        constructor
        · intro hxD
          by_contra hxS
          exact disjoint_left.1 hdis' (mem_compl.2 hxS) hxD
        · intro hxS
          exact (mem_union.1 hx).resolve_left (by simpa using hxS)
      exact this ▸ (mem_childClusters.1 hD').1
    refine ⟨Rᶜ, mem_unroot.2 (Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩), D', hsideOf hD', ?_, ?_⟩
    · refine disjoint_left.2 fun x hxR hxD => mem_compl.1 hxR ?_
      exact hun' ▸ mem_union_right _ hxD
    · ext x
      simp only [mem_union, mem_compl]
      constructor
      · rintro (hx | hx)
        · by_contra hxS
          exact hx (hcR.subset (mem_compl.2 hxS))
        · by_contra hxS
          exact disjoint_left.1 hdis' (mem_compl.2 hxS) hx
      · intro hxS
        by_cases hxR : x ∈ R
        · rw [← hun'] at hxR
          exact Or.inr ((mem_union.1 hxR).resolve_left (by simpa using hxS))
        · exact Or.inl hxR

/-- **A disjoint cover exists around every internal edge of a binary tree**, so that the selections of covers in `TOBQMC.consistency` and
the theorems around it can be made: the subsets of Algorithm 1, on the quadripartition of the edge, with any anchors. -/
theorem exists_isDisjointCover {T : Finset (Finset X)} (hT : IsBinaryTree T) {A : Finset X} (hA : A ∈ internalSides T) :
    ∃ Q, IsDisjointCover T A Q := by
  obtain ⟨hAT, h₁, h₂⟩ := mem_filter.mp hA
  have hAc : Aᶜ ∈ T := by
    obtain ⟨H, -, rfl, -⟩ := hT
    exact compl_mem_unroot.2 hAT
  obtain ⟨P₀, hP₀, P₁, hP₁, hd₀₁, hu₀₁⟩ := exists_blocks_of_isBinaryTree hT hAT h₁
  obtain ⟨P₂, hP₂, P₃, hP₃, hd₂₃, hu₂₃⟩ := exists_blocks_of_isBinaryTree hT hAc h₂
  have hsub₀ : P₀ ⊆ A := hu₀₁ ▸ subset_union_left
  have hsub₁ : P₁ ⊆ A := hu₀₁ ▸ subset_union_right
  have hsub₂ : P₂ ⊆ Aᶜ := hu₂₃ ▸ subset_union_left
  have hsub₃ : P₃ ⊆ Aᶜ := hu₂₃ ▸ subset_union_right
  have hAdis : ∀ {U W : Finset X}, U ⊆ A → W ⊆ Aᶜ → Disjoint U W := fun hU hW =>
    disjoint_left.2 fun x hx hx' => mem_compl.1 (hW hx') (hU hx)
  have hTu : IsUnrootedTree T := IsBinaryTree.isUnrootedTree hT
  have hne : ∀ {U : Finset X}, U ∈ T → U.Nonempty := fun hU =>
    (Level1.nonempty_of_mem_isUnrootedTree hTu hU).1
  let P : Fin 4 → Finset X := ![P₀, P₁, P₂, P₃]
  obtain ⟨z₀, hz₀⟩ := hne hP₀
  obtain ⟨z₁, hz₁⟩ := hne hP₁
  obtain ⟨z₂, hz₂⟩ := hne hP₂
  obtain ⟨z₃, hz₃⟩ := hne hP₃
  refine ⟨_, (threeFixOneAlter_isDisjointCover hT hA P ?_ ?_ hu₀₁ ?_ ![z₀, z₁, z₂, z₃] ?_).1⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact hd₀₁
      | exact hd₀₁.symm
      | exact hd₂₃
      | exact hd₂₃.symm
      | exact hAdis hsub₀ hsub₂
      | exact hAdis hsub₀ hsub₃
      | exact hAdis hsub₁ hsub₂
      | exact hAdis hsub₁ hsub₃
      | exact (hAdis hsub₀ hsub₂).symm
      | exact (hAdis hsub₀ hsub₃).symm
      | exact (hAdis hsub₁ hsub₂).symm
      | exact (hAdis hsub₁ hsub₃).symm
  · ext x
    simp only [mem_biUnion, mem_univ, true_and, iff_true]
    by_cases hx : x ∈ A
    · rw [← hu₀₁] at hx
      rcases mem_union.1 hx with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · have hx' : x ∈ P₂ ∪ P₃ := hu₂₃ ▸ mem_compl.2 hx
      rcases mem_union.1 hx' with h | h
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
  · intro i
    fin_cases i <;> first | exact hP₀ | exact hP₁ | exact hP₂ | exact hP₃
  · intro i
    fin_cases i <;> first | exact hz₀ | exact hz₁ | exact hz₂ | exact hz₃

/-! ### The modes of TOB-QMC -/

/-- The four-taxon subsets around the edge with side `A`: what TOB-QMC-exhaustive tests. -/
def aroundSets (A : Finset X) : Finset (Finset X) := (bipartitionQuartets A).image QuartetTree.taxa

theorem card_of_mem_aroundSets {A Y : Finset X} (hY : Y ∈ aroundSets A) : Y.card = 4 ∧ (A ∩ Y).card = 2 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hY
  exact ⟨s.card_taxa, s.card_of_mem (mem_filter.1 hs).2⟩

/-- A disjoint cover lies around the edge, so among the subsets of TOB-QMC-exhaustive. -/
theorem IsDisjointCover.subset_aroundSets {B : Finset (Finset X)} {A : Finset X} {Q : Finset (Finset X)}
    (h : IsDisjointCover B A Q) : Q ⊆ aroundSets A := by
  intro Y hY
  obtain ⟨s, hs, rfl⟩ := h.around Y hY
  exact mem_image.2 ⟨s, (mem_filter.1 hs).1, rfl⟩

/-- **TOB-QMC-exhaustive** (embedded lines 127-129), with the cut test: it tests all four-taxon subsets around each edge. They contain a disjoint
cover, by `exists_isDisjointCover`. -/
theorem consistency_implementation_exhaustive [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (mini : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B,
          IsMinimizerOf (fun Y => cutPValue c (ml c Y)) (aroundSets A) (mini c B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcImplementation (fun Y => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) Y))
            (starPValue .lrt (quartetCount unroot ω)) (α k) β (solve (quartetCount unroot ω)) aroundSets
            (mini (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  obtain ⟨α, hα₀, hαpos, h⟩ := consistency_implementation hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve mini hmini => ?_⟩
  refine h β hβ ml hml solve hsolve (fun _ _ A => aroundSets A) (fun _ B hB A hA => ?_)
    (fun _ _ _ A _ Y hY => card_of_mem_aroundSets hY) mini hmini
  obtain ⟨Q, hQ⟩ := exists_isDisjointCover hB hA
  exact ⟨Q, hQ.subset_aroundSets, hQ⟩

/-- **TOB-QMC-3f1a** (embedded lines 129-130), with the cut test: it tests Algorithm 1's subsets around each edge, on the blocks `P B A` of the
quadripartition, with anchors `z B A`. -/
theorem consistency_implementation_threeFixOneAlter [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E}
    {ρ : ℝ} (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (P : Finset (Finset X) → Finset X → Fin 4 → Finset X) (z : Finset (Finset X) → Finset X → Fin 4 → X),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B,
          (∀ i j, i ≠ j → Disjoint (P B A i) (P B A j)) ∧ univ.biUnion (P B A) = univ ∧
            P B A 0 ∪ P B A 1 = A ∧ (∀ i, P B A i ∈ B) ∧ ∀ i, z B A i ∈ P B A i) →
      ∀ (mini : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B,
          IsMinimizerOf (fun Y => cutPValue c (ml c Y)) (threeFixOneAlter (P B A) (z B A)) (mini c B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcImplementation (fun Y => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) Y))
            (starPValue .lrt (quartetCount unroot ω)) (α k) β (solve (quartetCount unroot ω))
            (fun A => threeFixOneAlter (P (solve (quartetCount unroot ω)) A) (z (solve (quartetCount unroot ω)) A))
            (mini (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  obtain ⟨α, hα₀, hαpos, h⟩ := consistency_implementation hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve P z hPz mini hmini => ?_⟩
  have hcov : ∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (threeFixOneAlter (P B A) (z B A)) := by
    intro B hB A hA
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hPz B hB A hA
    exact (threeFixOneAlter_isDisjointCover hB hA (P B A) h₁ h₂ h₃ h₄ (z B A) h₅).1
  refine h β hβ ml hml solve hsolve (fun _ B A => threeFixOneAlter (P B A) (z B A))
    (fun _ B hB A hA => ⟨_, Subset.rfl, hcov B hB A hA⟩) (fun _ B hB A hA Y hY => ?_) mini hmini
  obtain ⟨s, hs, rfl⟩ := (hcov B hB A hA).around Y hY
  exact ⟨s.card_taxa, s.card_of_mem (mem_filter.1 (mem_filter.1 hs).1).2⟩

/-- **The combination of Algorithm 2 with 3f1a** (embedded lines 622-623), with the star test on the minimizer as implemented, and the cut
test: Algorithm 2 runs on the p-value of the treelikeness test alone, which does not depend on `α`, `β`, and the minimizer is over the
subsets it tested and the disjoint cover. -/
theorem consistency_implementation_search [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E} {ρ : ℝ}
    (hStd : StandardAssumptions N θ ρ) (hLevel : IsLevelOne N)
    (hNon : IsTQuartetNonanomalous N (nmscCF N θ ρ))
    (hBlob : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      AllmanEtAl2023.IsNonCut (nmscCF N θ ρ) q) (hX : 4 ≤ Fintype.card X) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ k, 0 < α k) ∧
      ∀ (β : ℝ), 0 < β →
      ∀ (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X), IsMLSelection ml →
      ∀ (solve : (QuartetTree X → ℝ) → Finset (Finset X)), (∀ c, IsWQCOptimal c (solve c)) →
      ∀ (cover : Finset (Finset X) → Finset X → Finset (Finset X)),
        (∀ B, IsBinaryTree B → ∀ A ∈ internalSides B, IsDisjointCover B A (cover B A)) →
      ∀ (argmin : (SearchTuple X → ℝ) → Finset (SearchTuple X) → SearchTuple X), (∀ p, IsArgmin p (argmin p)) →
      ∀ (limit : ℕ) (pick : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → ℕ → SearchTuple X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B, ∀ i, (pick c B A i).IsAround A) →
      ∀ (mini : (QuartetTree X → ℝ) → Finset (Finset X) → Finset X → Finset X),
        (∀ c B, IsBinaryTree B → ∀ A ∈ internalSides B,
          IsMinimizerOf (fun Y => cutPValue c (ml c Y))
            (cover B A ∪ (bipartitionSearch A (fun t => cutPValue c (ml c t.taxa))
              (argmin fun t => cutPValue c (ml c t.taxa)) limit (pick c B A)).testedSets) (mini c B A)) →
        Tendsto (fun k => iidProb (geneTreeDist N θ ρ) k fun ω =>
          tobqmcImplementation (fun Y => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) Y))
            (starPValue .lrt (quartetCount unroot ω)) (α k) β (solve (quartetCount unroot ω))
            (fun A => cover (solve (quartetCount unroot ω)) A ∪
              (bipartitionSearch A (fun t => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) t.taxa))
                (argmin fun t => cutPValue (quartetCount unroot ω) (ml (quartetCount unroot ω) t.taxa)) limit
                (pick (quartetCount unroot ω) (solve (quartetCount unroot ω)) A)).testedSets)
            (mini (quartetCount unroot ω) (solve (quartetCount unroot ω))) = treeOfBlobs N) atTop (𝓝 1) := by
  obtain ⟨α, hα₀, hαpos, h⟩ := consistency_implementation hStd hLevel hNon hBlob hX
  refine ⟨α, hα₀, hαpos, fun β hβ ml hml solve hsolve cover hcover argmin hargmin limit pick hpick mini hmini => ?_⟩
  refine h β hβ ml hml solve hsolve (fun c B A => cover B A ∪ (bipartitionSearch A (fun t => cutPValue c (ml c t.taxa))
    (argmin fun t => cutPValue c (ml c t.taxa)) limit (pick c B A)).testedSets)
    (fun _ B hB A hA => ⟨cover B A, subset_union_left, hcover B hB A hA⟩) (fun c B hB A hA Y hY => ?_) mini hmini
  rcases mem_union.1 hY with hY | hY
  · obtain ⟨s, hs, rfl⟩ := (hcover B hB A hA).around Y hY
    exact ⟨s.card_taxa, s.card_of_mem (mem_filter.1 (mem_filter.1 hs).1).2⟩
  · exact card_of_mem_testedSets (hargmin _) (hpick c B hB A hA) hY

/-! ### The star test at level `β = 1`

TOB-QMC's text at embedded lines 171-172: "setting `β = 1` ensures the null of the star test is always rejected so branches are never
contracted based on it". The star test rejects when its p-value is below `β`. -/

/-- On three equal counts the star test has p-value `1`, so at `β = 1` it does not reject: "always rejected" fails on these counts. -/
theorem starPValue_eq_one_of_forall_eq {c : QuartetTree X → ℝ} {q : Finset X} (hq : q.card = 4) {m : ℝ}
    (h : ∀ r ∈ treesOn q, c r = m) : starPValue .lrt c q = 1 := by
  have hsum : ∑ r ∈ treesOn q, c r = 3 * m := by
    rw [sum_congr rfl h, sum_const, card_treesOn hq]
    simp
  have hlog : ∑ r ∈ treesOn q, c r * Real.log (c r) = 3 * (m * Real.log m) := by
    rw [sum_congr rfl fun r hr => by rw [h r hr], sum_const, card_treesOn hq]
    simp
  have hstat : starStat c q = 0 := by
    rw [starStat, hlog, hsum, mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  simp [starPValue, chiSqTwoTail, hstat]

/-- On counts not all equal, the star test has p-value below `1`: at `β = 1` it rejects. So the claim at embedded lines 171-172 holds on
these counts, which are all the counts when their total is not a multiple of three. -/
theorem starPValue_lt_one {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {q : Finset X} (hq : q.card = 4)
    (hne : ∃ r ∈ treesOn q, ∃ r' ∈ treesOn q, c r ≠ c r') : starPValue .lrt c q < 1 := by
  set S := ∑ r ∈ treesOn q, c r with hS
  have hS₀ : 0 ≤ S := sum_nonneg fun r _ => hc r
  have hSpos : 0 < S := by
    refine lt_of_le_of_ne hS₀ fun h => ?_
    have hz := (sum_eq_zero_iff_of_nonneg fun r _ => hc r).1 h.symm
    obtain ⟨r, hr, r', hr', hrr⟩ := hne
    exact hrr ((hz r hr).trans (hz r' hr').symm)
  have hscaled : 0 < starStat (fun r => S⁻¹ * c r) q := by
    refine QuartetTests.starStat_pos _ (fun r => mul_nonneg (inv_nonneg.2 hS₀) (hc r)) hq ?_ ?_
    · rw [← mul_sum, ← hS, inv_mul_cancel₀ hSpos.ne']
    · by_contra hall
      push Not at hall
      obtain ⟨r, hr, r', hr', hrr⟩ := hne
      have h₁ := hall r hr
      have h₂ := hall r' hr'
      exact hrr (mul_left_cancel₀ (inv_ne_zero hSpos.ne') (h₁.trans h₂.symm))
  rw [QuartetTests.starStat_const_mul (inv_ne_zero hSpos.ne')] at hscaled
  have hstat : 0 < starStat c q := (mul_pos_iff_of_pos_left (inv_pos.2 hSpos)).1 hscaled
  simp only [starPValue, chiSqTwoTail]
  exact Real.exp_lt_one_iff.2 (by linarith)

end TOBQMC
