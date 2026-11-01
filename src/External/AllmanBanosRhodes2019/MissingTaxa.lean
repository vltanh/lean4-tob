module

public import Basic.Testing.MissingTaxa
public import External.AllmanBanosRhodes2019.Proposition9
public import TINNiK.MissingTaxa

/-!
# NANUQ with gene trees on subsets of the taxa

The source's algorithm takes "a collection of unrooted topological gene trees on subsets of a taxon set `X`, such that each 4-element subset of `X`
appears on at least one tree" (line 1758), and its Step 1 says "If all four taxa are not on a gene tree, that tree does not contribute to the counts". Its
Theorem 36 speaks of "`m` gene trees independently drawn" and does not treat missing taxa; "many missing taxa on gene trees" is on its list of
sources of error (line 2230).

The procedure is Steps 2 and 3 on the counts of `Phylogenetics.quartetCountOn`, since `classify` takes the counts as an argument. What a source of
this kind leaves to the reader is that the theorem carries over, when each set of four taxa is on more and more gene trees
(`TINNiK.Covers`). So is it here: `theorem36_missing`, by the source's proof, on the gene trees containing each set of four taxa, which are an
independent sample (`Phylogenetics.iidProb_quartetCountOn`).

With a set of four taxa on no gene tree, the star test has p-value `1`, and on one gene tree `1/3` (`TINNiK.starPValue_of_forall_eq_zero`,
`TINNiK.mem_testedB_of_coverCount_eq_one`): it is classified as a star tree at low levels `β`, so "appears on at least one tree" makes the algorithm
meaningful, and is not what the consistency theorem needs.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace External.AllmanBanosRhodes2019

variable {X : Type*} [Fintype X] [DecidableEq X]

section Sample

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)} {on : (m : ℕ) → Fin m → Finset X}

/-- The levels `α` make the second test reject off its null, with the taxa `on` kept. Parallel to `RejectsOffNull`. -/
def RejectsOffNullOn (dist : Γ → ℝ) (sides : Γ → Finset (Finset X)) (on : (m : ℕ) → Fin m → Finset X) (α : ℕ → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ IsT3Null (displayCF dist sides) q →
    Tendsto (fun m => iidProb dist m fun ω => ∀ u ∈ treesOn q, t3PValue (quartetCountOn sides (on m) ω) u < α m) atTop (𝓝 1)

/-- **The levels of Theorem 36 with missing taxa**: as `exists_levels`, the sample size in the level of each set of four taxa being the number of gene trees
containing it. -/
theorem exists_levels_on (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) (hon : TINNiK.Covers on) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧ (∀ᶠ m in atTop, α m < 1) ∧ RejectsOffNullOn dist sides on α := by
  set p := displayCF dist sides with hp
  let Q : Finset (Finset X) := univ.filter fun q => q.card = 4 ∧ ¬ IsT3Null p q
  have hQ : ∀ q ∈ Q, 0 < t3Stat p q / 2 := fun q hq => by
    obtain ⟨hq4, hn⟩ := (mem_filter.mp hq).2
    exact half_pos (t3Stat_pos_of_not_isT3Null hd hs hq4 hn)
  let α : ℕ → ℝ := fun m => Q.fold max (chiSqTwoTail (m * 1)) fun q =>
    chiSqTwoTail ((coverCount (on m) q : ℕ) * (t3Stat p q / 2))
  have hle : ∀ m : ℕ, ∀ q ∈ Q, chiSqTwoTail ((coverCount (on m) q : ℕ) * (t3Stat p q / 2)) ≤ α m := fun m q hq =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, le_rfl⟩)
  have hbase : ∀ m : ℕ, chiSqTwoTail (m * 1) ≤ α m := fun m => (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  have hpos : ∀ t : ℝ, 0 < chiSqTwoTail t := fun t => Real.exp_pos _
  have hlt1 : ∀ {n : ℕ} {d : ℝ}, 1 ≤ n → 0 < d → chiSqTwoTail (n * d) < 1 := by
    intro n d hn hd0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    unfold chiSqTwoTail
    rw [Real.exp_lt_one_iff]
    have := mul_pos hn' hd0
    linarith
  refine ⟨α, ?_, fun m => (hpos _).trans_le (hbase m), ?_, ?_⟩
  · have hsum : Tendsto (fun m : ℕ => chiSqTwoTail (m * 1) +
        ∑ q ∈ Q, chiSqTwoTail ((coverCount (on m) q : ℕ) * (t3Stat p q / 2))) atTop (𝓝 0) := by
      have := (TINNiK.tendsto_chiSqTwoTail_comp (k := id) tendsto_id one_pos).add
        (tendsto_finsetSum Q fun q hq => TINNiK.tendsto_chiSqTwoTail_comp (hon q (mem_filter.mp hq).2.1) (hQ q hq))
      simpa using this
    refine squeeze_zero (fun m => (hpos _).le.trans (hbase m)) (fun m => ?_) hsum
    refine (Finset.fold_max_le _).mpr ⟨?_, fun q hq => ?_⟩
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (hpos _).le)
    · exact (Finset.single_le_sum (f := fun q => chiSqTwoTail ((coverCount (on m) q : ℕ) * (t3Stat p q / 2)))
        (fun _ _ => (hpos _).le) hq).trans (le_add_of_nonneg_left (hpos _).le)
  · have hev : ∀ᶠ m in atTop, ∀ q ∈ Q, 1 ≤ coverCount (on m) q := by
      rw [Finset.eventually_all]
      intro q hq
      exact (hon q (mem_filter.mp hq).2.1).eventually (eventually_ge_atTop 1)
    filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    exact (Finset.fold_max_lt _).mpr ⟨hlt1 hm1 one_pos, fun q hq => hlt1 (hm q hq) (hQ q hq)⟩
  · intro q hq4 hn
    have hq : q ∈ Q := mem_filter.mpr ⟨mem_univ _, hq4, hn⟩
    have hEv : ∀ n : ℕ, DependsOnTaxa q fun c => ∀ u ∈ treesOn q, t3PValue c u < chiSqTwoTail (n * (t3Stat p q / 2)) :=
      fun n c c' hcc => forall₂_congr fun u hu => by rw [t3PValue_congr hu hcc]
    have h := tendsto_iidProb_on hd sides (hon q hq4) (on := on) hEv (tendsto_t3PValue_lt_level hd hs hq4 hn)
    exact tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω u hu => (hω u hu).trans_le (hle m q hq)) h

/-- On a set of four taxa, Step 2 gives the population value, with missing taxa, with probability tending to one. Parallel to
`tendsto_classify_eq_cfClass_at`, at a fixed level `β` as in the source's Theorem 36. -/
theorem tendsto_classify_eq_cfClass_on (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides)
    (hpos : ∀ r, 0 < displayCF dist sides r) (hon : TINNiK.Covers on) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : RejectsOffNullOn dist sides on α) {β : ℝ} (hβ : 0 < β) (hcen : TINNiK.NoCentroidCF (displayCF dist sides))
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun m => iidProb dist m fun ω =>
      classify mlT mlC (α m) β (quartetCountOn sides (on m) ω) q = cfClass (displayCF dist sides) q) atTop (𝓝 1) := by
  have hk := hon q hq
  have hstar : Tendsto (fun m => iidProb dist m fun ω => starPValue .lrt (quartetCountOn sides (on m) ω) q < β) atTop (𝓝 1) :=
    tendsto_iidProb_on (Ev := fun _ c => starPValue .lrt c q < β) hd sides hk
      (fun _ c c' hcc => by
        change starPValue .lrt c q < β ↔ starPValue .lrt c' q < β
        rw [starPValue_lrt_congr hcc])
      (tendsto_starPValue_lt hd hs hq (hcen q hq) (β := fun _ => β) (fun _ => hβ) (tendsto_log_const_div β))
  rcases cf_trichotomy hq (QuartetTests.sum_displayCF_treesOn hd hs hq) with
    huni | ⟨s, hsq, hstrict⟩ | ⟨hnull, s, hsq, hmin⟩
  · exact absurd huni (hcen q hq)
  · have hst : s.taxa = q := mem_treesOn.1 hsq
    subst hst
    rw [cfClass_eq_tree hsq hstrict]
    have hal : ∀ r ∈ s.alternatives, r ∈ treesOn s.taxa := fun r hr =>
      mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1
    have hnull := tendsto_iidProb_on_level hd sides hk (on := on)
      (G := fun c => ∀ r ∈ s.alternatives, t1Stat c s < t1Stat c r) (f := fun c => t3PValue c s)
      (fun c c' hcc => forall₂_congr fun r hr => by rw [t1Stat_congr hsq hcc, t1Stat_congr (hal r hr) hcc])
      (fun c c' hcc => t3PValue_congr hsq hcc)
      (fun a ha => QuartetTests.t3Test_null hd hs hstrict (fun r _ => hpos r) ha) hα₀
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_) (tendsto_iidProb_and hd hstar hnull)
    obtain ⟨h₁, h₂, h₃⟩ := hω
    set c := quartetCountOn sides (on m) ω
    have hc : ∀ r, 0 ≤ c r := quartetCountOn_nonneg sides (on m) ω
    have hmax : mlT c s.taxa = s := by
      obtain ⟨hm, hmx⟩ := hmlT c s.taxa s.card_taxa
      by_contra hne
      have hrt := mem_treesOn.1 hm
      have halt := QuartetTree.mem_alternatives.2 ⟨hrt, hne⟩
      have hle := QuartetTests.t1Stat_le_t1Stat_of_max hc (s := mlT c s.taxa) (r := s)
        (fun u hu => hmx u (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hu).1.trans hrt)))
        (mem_treesOn.2 hrt.symm)
      exact absurd (h₂ _ halt) (not_lt.2 hle)
    rw [classify, ite_eq_right (not_le.2 h₁), hmax, ite_eq_left h₃]
  · have hst : s.taxa = q := mem_treesOn.1 hsq
    subst hst
    rw [cfClass_eq_cycle hsq hmin]
    have hal : ∀ r ∈ s.alternatives, r ∈ treesOn s.taxa := fun r hr =>
      mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1
    have hF : ∀ᶠ x in 𝓝 (displayCF dist sides), ∀ r ∈ s.alternatives, x s < x r := by
      rw [Finset.eventually_all]
      intro r hr
      exact ((continuous_apply s).tendsto _).eventually_lt ((continuous_apply r).tendsto _) (hmin r hr)
    have hfreq : Tendsto (fun n => iidProb dist n fun η => ∀ r ∈ s.alternatives,
        quartetCount sides η s < quartetCount sides η r) atTop (𝓝 1) := by
      refine tendsto_iidProb_of_imp hd ?_ (QuartetTests.tendsto_iidProb_freq hd hF)
      filter_upwards [eventually_gt_atTop 0] with n hn0 ω hω r hr
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      exact (div_lt_div_iff_of_pos_right hn').1 (hω r hr)
    have hminOn := tendsto_iidProb_on (Ev := fun _ c => ∀ r ∈ s.alternatives, c s < c r) hd sides hk (on := on)
      (fun _ c c' hcc => forall₂_congr fun r hr => by rw [hcc s hsq, hcc r (hal r hr)]) hfreq
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
      (tendsto_iidProb_and hd hstar (tendsto_iidProb_and hd (hrej _ hq hnull) hminOn))
    obtain ⟨h₁, h₂, h₃⟩ := hω
    set c := quartetCountOn sides (on m) ω
    have hmin' : mlC c s.taxa = s := by
      obtain ⟨hm, hle⟩ := hmlC c s.taxa s.card_taxa
      by_contra hne
      exact absurd (hle s (mem_treesOn.2 rfl)) (not_le.2 (h₃ _ (QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hm, hne⟩)))
    rw [classify, ite_eq_right (not_le.2 h₁), ite_eq_right (not_le.2 (h₂ _ (hmlT _ _ hq).1)), hmin']

end Sample

section Network

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} {θ : MetricData E}

/-- **Theorem 36 with gene trees on subsets of the taxa** (`nanuq:theorem36`), with what it uses of Proposition 9: under the hypotheses of
`theorem36_of_proposition9`, for gene trees with the taxa `on` kept, each set of four taxa being on more and more of them, there are levels
`α_m → 0` such that Steps 2 and 3 of NANUQ on the counts of Step 1 give the network's classes and its theoretical distance, with probability tending
to one. -/
theorem theorem36_missing_of_proposition9 [Nonempty X] (hN : N.IsPhylogenetic) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (hP9 : Proposition9 N (nmscCF N θ 0)) (h32 : ThreeTwoTreelike N (nmscCF N θ 0))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0)) {on : (m : ℕ) → Fin m → Finset X} (hon : TINNiK.Covers on) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ᶠ m in atTop, α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          (∀ q : Finset X, q.card = 4 →
            classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω) q = networkClass N q) ∧
            nanuqDistance (classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω)) = networkDistance N)
          atTop (𝓝 1) := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hd := isDist_geneTreeDist hN hθ hρ
  obtain ⟨α, hα₀, hαpos, hαlt, hrej⟩ := exists_levels_on hd (TINNiK.displaysOne_nmsc (θ := θ) (ρ := 0) hN) hon
  refine ⟨α, hαpos, hαlt, hα₀, fun β hβ _ mlT mlC hmlT hmlC => ?_⟩
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ?_)
    (tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
      (fun q m ω => classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω) q.val =
        cfClass (displayCF (geneTreeDist N θ 0) unroot) q.val)
      fun q => tendsto_classify_eq_cfClass_on hd (TINNiK.displaysOne_nmsc hN) (fun r => nmscCF_pos hN hθ hρ r) hon hα₀ hrej hβ hcen
        hmlT hmlC q.property)
  have hall : ∀ q : Finset X, q.card = 4 →
      classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω) q = networkClass N q := fun q hq =>
    (hω ⟨q, hq⟩).trans (cfClass_eq_networkClass hN hLevel hθ hρ hP9 h32 hcen hq)
  exact ⟨hall, nanuqDistance_congr hall⟩

/-- **Theorem 36 with gene trees on subsets of the taxa** (`nanuq:theorem36`). Parallel to `theorem36`, with Proposition 9 proved. -/
theorem theorem36_missing [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) (hθ : N.IsMetric θ)
    (h32 : ThreeTwoTreelike N (nmscCF N θ 0)) (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0))
    {on : (m : ℕ) → Fin m → Finset X} (hon : TINNiK.Covers on) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ᶠ m in atTop, α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          (∀ q : Finset X, q.card = 4 →
            classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω) q = networkClass N q) ∧
            nanuqDistance (classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω)) = networkDistance N)
          atTop (𝓝 1) :=
  theorem36_missing_of_proposition9 hN hLevel hθ (proposition9 hN hBin hLevel hθ ⟨le_rfl, zero_le_one⟩) h32 hcen hon

/-- **Theorem 36 for generic parameters, with gene trees on subsets of the taxa** (`nanuq:theorem36`), with the hypothesis as printed. Parallel to
`theorem36_generic`. -/
theorem theorem36_generic_missing [Nonempty X] (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (hLevel : IsLevelOne N) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → ThreeTwoTreelike N (nmscCF N θ 0) →
      ∀ on : (m : ℕ) → Fin m → Finset X, TINNiK.Covers on →
      ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ᶠ m in atTop, α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
        ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
          IsMaxCountSelection mlT → IsMinCountSelection mlC →
          Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
            nanuqDistance (classify mlT mlC (α m) β (quartetCountOn unroot (on m) ω)) = networkDistance N)
            atTop (𝓝 1) := by
  refine ⟨_, TINNiK.isGenericNull_centroid hN hBin, fun θ hθ hA h32 on hon => ?_⟩
  have hcen : TINNiK.NoCentroidCF (nmscCF N θ 0) := by
    by_contra hn
    exact hA ⟨hθ, hn⟩
  obtain ⟨α, hαpos, hαlt, hα₀, h⟩ := theorem36_missing hN hBin hLevel hθ h32 hcen hon
  refine ⟨α, hαpos, hαlt, hα₀, fun β hβ hβ₁ mlT mlC hmlT hmlC => ?_⟩
  exact tendsto_iidProb_of_imp (isDist_geneTreeDist hN hθ ⟨le_rfl, zero_le_one⟩)
    (Eventually.of_forall fun m ω hω => hω.2) (h β hβ hβ₁ mlT mlC hmlT hmlC)

end Network

end External.AllmanBanosRhodes2019
