module

public import Phylogenetics.NMSC.DisplayedTreeModel

/-!
# Ané, Fogg, Allman, Baños, Rhodes 2024: Proposition 12

C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the multispecies coalescent: theory and
prevalence*, J. Math. Biol. 88 (2024), https://doi.org/10.1007/s00285-024-02050-7, read in its bioRxiv text
(10.1101/2023.08.18.553582).

"Under the common inheritance model with `ρ = 1`, a 4-taxon binary metric network is not anomalous." The proof is the
source's. With `ρ = 1` a gene tree evolves along one displayed tree, so `qCF(N) = ∑ γ(T) qCF(T)` (`nmscCF_rho_one`). In
each displayed tree, a topology that this tree does not display has an entry at most the other two
(`nmscCF_choiceMetric_le_of_not_displays`), so the same holds of the convex sum. This one step is both halves of the
printed proof:

* class 1: the displayed topology has at least the entries of the two others, so at least `1/3`
  (`proposition12_class1`);
* class 2: the topology `T₃` not displayed has at most the entries of the two others (`proposition12_class2`).

Being binary is not used: on a nonbinary network, a displayed tree may leave the four taxa unresolved, and then its
entries are all `1/3`. The strict form on cut-edge splits is `Phylogenetics.RootedNetwork.nmscCF_lt_rho_one` in
`src/Basic/RhoOne.lean`.

The lengths of hybrid arcs may vanish, and a hybrid arc of length zero is a tree arc of length zero in a displayed tree, so
the comparison in a displayed tree is made at positive lengths, and passes to the limit, as
`Phylogenetics.RootedNetwork.one_sub_exp_le_sub_nmscCF_rho_one` does in the library.

## Main results

* `IsDisplayed`, `displayedQuartets`: the topologies induced by the trees displayed in a network, and so its class.
* `IsAnomalous`: Definition 1 of the source on a set of four taxa; `IsAnomalousClassTwo`: Definition 2 at class 2.
* `nmscCF_rho_one_le_of_not_isDisplayed`: the step above.
* `proposition12`, `proposition12_class1`, `proposition12_class2`.
-/

@[expose] public noncomputable section

open Finset Phylogenetics Phylogenetics.RootedNetwork
open scoped Classical

namespace External.AneEtAl2024

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : MetricData E}

/-- The quartet tree `s` is induced by a tree displayed in `N`: one parent choice keeps a tree displaying it. -/
def IsDisplayed (N : RootedNetwork V E X) (s : QuartetTree X) : Prop :=
  ∃ c : N.ParentChoice, Displays (N.displayedSides c) s

/-- The topologies on the four taxa `q` induced by the trees displayed in `N`. "A 4-taxon network `N` is of class `k` if
there are `k` distinct unrooted binary topologies induced by its displayed trees" is `(displayedQuartets N q).card = k`. -/
def displayedQuartets (N : RootedNetwork V E X) (q : Finset X) : Finset (QuartetTree X) :=
  (treesOn q).filter (IsDisplayed N)

/-- **Definition 1** of the source (`ext:ane2024-definition1`), on the four taxa `q`: `N` is (hard-)anomalous under
`NMSC(ρ)` on `q` when a topology `T₁` induced by a displayed tree is less probable than a topology `T₂` that no displayed
tree induces. -/
def IsAnomalous (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ) (q : Finset X) : Prop :=
  ∃ T₁ ∈ treesOn q, ∃ T₂ ∈ treesOn q, IsDisplayed N T₁ ∧ ¬ IsDisplayed N T₂ ∧ nmscCF N θ ρ T₁ < nmscCF N θ ρ T₂

/-- **Definition 2** of the source at class 2 (`ext:ane2024-definition2`): `P(T₃) > min{P(T₁), P(T₂)}`, where `T₃` is the
topology not induced by displayed trees, and `T₁`, `T₂` are the two others. -/
def IsAnomalousClassTwo (N : RootedNetwork V E X) (θ : MetricData E) (ρ : ℝ) (q : Finset X) : Prop :=
  (displayedQuartets N q).card = 2 ∧ ∃ T₃ ∈ treesOn q, ¬ IsDisplayed N T₃ ∧
    ∃ T₁ ∈ T₃.alternatives, ∃ T₂ ∈ T₃.alternatives, T₁ ≠ T₂ ∧
      min (nmscCF N θ ρ T₁) (nmscCF N θ ρ T₂) < nmscCF N θ ρ T₃

omit [Fintype V] [Fintype E] [Fintype X] in
/-- A second quartet tree on the same taxa is an alternative. -/
theorem mem_alternatives_of_ne [Fintype X] {q : Finset X} {s t : QuartetTree X} (hs : s ∈ treesOn q) (ht : t ∈ treesOn q)
    (h : t ≠ s) : t ∈ s.alternatives :=
  QuartetTree.mem_alternatives.2 ⟨(mem_treesOn.1 ht).trans (mem_treesOn.1 hs).symm, h⟩

/-- **The entries of `qCF(T)` for a displayed tree `T`**, at positive lengths: a topology that `T` does not display has an
entry at most those of the other topologies on the four taxa. If `T` displays a topology `s` on them, then `s` has the largest
entry and its two alternatives are equal, as in the source's "the third entry in `qCF(T)` is smaller than or equal to the first
and second entries"; if `T` leaves the four taxa unresolved, all entries are `1/3`. -/
theorem nmscCF_choiceMetric_le_of_not_displays (hN : N.IsPhylogenetic) (c : N.ParentChoice) (hℓ : ∀ f, 0 < θ.length f)
    {q : Finset X} (hq : q.card = 4) {t r : QuartetTree X} (ht : t ∈ treesOn q) (hr : r ∈ treesOn q)
    (hnt : ¬ Displays (N.displayedSides c) t) :
    nmscCF N (N.choiceMetric θ c) 1 t ≤ nmscCF N (N.choiceMetric θ c) 1 r := by
  by_cases hex : ∃ s ∈ treesOn q, Displays (N.displayedSides c) s
  · obtain ⟨s, hs, hd⟩ := hex
    have hts : t ≠ s := fun h => hnt (h ▸ hd)
    have htalt := mem_alternatives_of_ne hs ht hts
    obtain ⟨P, hP, e, he, hb, hn⟩ := exists_isKeptArc_of_displays hN hd
    obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
    have hM := isPhylogenetic_choiceNetwork hN c a
    have hμ := isMetric_choiceNetworkMetric hN c a (θ := θ) fun f _ => hℓ f
    have htree : ∀ f g, (N.choiceNetwork hN c a).graph.target f = (N.choiceNetwork hN c a).graph.target g → f = g :=
      fun f g h => eq_of_target_choiceNetwork hN c a h
    have hbM : ∀ x ∈ P, (N.choiceNetwork hN c a).IsBelow ⟨e, he⟩ x := fun x hx =>
      reaches_choiceNetwork hN c a _ _ (hb x hx)
    have hnM : ∀ x ∈ s.taxa, x ∉ P → ¬ (N.choiceNetwork hN c a).IsBelow ⟨e, he⟩ x := fun x hx hxP hb' =>
      hn x hx hxP (reachesOff_of_reaches_choiceNetwork hN c a hb')
    by_cases hrs : r = s
    · subst hrs
      have hbound := one_sub_exp_le_sub_nmscCF_of_tree hM hμ ⟨zero_le_one, le_rfl⟩ htree r hP hbM hnM htalt
      rw [nmscCF_choiceNetwork hN c a zero_le_one θ r, nmscCF_choiceNetwork hN c a zero_le_one θ t] at hbound
      have hexp : Real.exp (-(N.choiceNetworkMetric θ c).length ⟨e, he⟩) < 1 :=
        Real.exp_lt_one_iff.2 (neg_lt_zero.2 (hℓ e))
      linarith
    · have hralt := mem_alternatives_of_ne hs hr hrs
      -- the two alternatives of the displayed topology are equal, by `NMSC.cut_alternatives` on the tree of the choice
      have hcut : InducedCutSplit (N.choiceNetwork hN c a) s := by
        refine ⟨P, hP, (hasCutSplitOn_iff_separates hM _ _).2 ⟨⟨e, he⟩, Or.inl ?_⟩⟩
        have hinter : (s.taxa : Set X) ∩ (P : Set X) = (P : Set X) :=
          Set.inter_eq_right.2 (coe_subset.2 (s.subset_taxa hP))
        rw [hinter]
        refine ⟨⟨a, mem_coe.2 ha⟩, ?_, ?_⟩
        · exact fun x hx => not_avoidingReach_of_tree hM htree (hbM x (mem_coe.1 hx))
        · rintro x ⟨hxq, hxP⟩
          exact hnM x (mem_coe.1 hxq) (fun h => hxP (mem_coe.2 h))
      have heq := NMSC.cut_alternatives hM hμ ⟨zero_le_one, le_rfl⟩ s hcut t htalt r hralt
      rw [nmscCF_choiceNetwork hN c a zero_le_one θ t, nmscCF_choiceNetwork hN c a zero_le_one θ r] at heq
      exact heq.le
  · push Not at hex
    rw [nmscCF_choiceMetric_eq_third hN c hℓ hq hex ht, nmscCF_choiceMetric_eq_third hN c hℓ hq hex hr]

/-- `nmscCF_rho_one_le_of_not_isDisplayed` at positive lengths: "since `qCF(N)` is a convex sum, the same holds for `N`". -/
theorem nmscCF_rho_one_le_of_pos (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hℓ : ∀ f, 0 < θ.length f)
    {q : Finset X} (hq : q.card = 4) {t r : QuartetTree X} (ht : t ∈ treesOn q) (hr : r ∈ treesOn q)
    (hnt : ¬ IsDisplayed N t) : nmscCF N θ 1 t ≤ nmscCF N θ 1 r := by
  rw [nmscCF_rho_one hN hθ.isNormalized t, nmscCF_rho_one hN hθ.isNormalized r]
  refine sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (choiceWeight_nonneg hθ c)
  exact nmscCF_choiceMetric_le_of_not_displays hN c hℓ hq ht hr fun h => hnt ⟨c, h⟩

/-- **The step of the source's proof of Proposition 12, for every class**: at `ρ = 1`, for any weak parameters, a topology that no
displayed tree induces has probability at most that of each topology on the same four taxa. The lengths go down to those of `θ` by
continuity. -/
theorem nmscCF_rho_one_le_of_not_isDisplayed (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {q : Finset X}
    (hq : q.card = 4) {t r : QuartetTree X} (ht : t ∈ treesOn q) (hr : r ∈ treesOn q) (hnt : ¬ IsDisplayed N t) :
    nmscCF N θ 1 t ≤ nmscCF N θ 1 r := by
  have hℓ : ∀ f, AnalyticOnNhd ℝ (fun ε : ℝ => (addLength θ ε).length f) Set.univ := fun f =>
    analyticOnNhd_const.add analyticOnNhd_id
  have hγ : ∀ f, AnalyticOnNhd ℝ (fun ε : ℝ => (addLength θ ε).inheritance f) Set.univ := fun f =>
    analyticOnNhd_const
  have hcont : ∀ u : QuartetTree X, Continuous fun ε : ℝ => nmscCF N (addLength θ ε) 1 u := fun u =>
    continuousOn_univ.1 (analyticOnNhd_nmscCF N (θ := addLength θ) 1 hℓ hγ u).continuousOn
  have hlim : ∀ u : QuartetTree X, Filter.Tendsto (fun ε : ℝ => nmscCF N (addLength θ ε) 1 u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (nmscCF N θ 1 u)) := fun u => by
    have h0 := (hcont u).tendsto 0
    rw [addLength_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto (hlim t) (hlim r) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  exact nmscCF_rho_one_le_of_pos (θ := addLength θ ε) hN ⟨fun f => add_nonneg (hθ.1 f) hε'.le, hθ.2.1, hθ.2.2⟩
    (fun f => add_pos_of_nonneg_of_pos (hθ.1 f) hε') hq ht hr hnt

/-- **Proposition 12** (`ext:ane2024-proposition12`), with Definition 1: under the common inheritance model with `ρ = 1`, a network with
weak parameters is not anomalous on any four taxa. The source states it for a 4-taxon binary metric network: `q` is then all the taxa,
and being binary is not used. -/
theorem proposition12 (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {q : Finset X} (hq : q.card = 4) :
    ¬ IsAnomalous N θ 1 q := by
  rintro ⟨T₁, hT₁, T₂, hT₂, -, hnd, hlt⟩
  exact absurd hlt (not_lt.2 (nmscCF_rho_one_le_of_not_isDisplayed hN hθ hq hT₂ hT₁ hnd))

/-- **Proposition 12, class 2** (`ext:ane2024-proposition12`), with Definition 2: the printed case "if `N` is of class 2". The topology
`T₃` that no displayed tree induces has `P(T₃) ≤ min{P(T₁), P(T₂)}`. -/
theorem proposition12_class2 (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {q : Finset X} (hq : q.card = 4) :
    ¬ IsAnomalousClassTwo N θ 1 q := by
  rintro ⟨-, T₃, hT₃, hnd, T₁, hT₁, T₂, hT₂, -, hlt⟩
  have h₁ := nmscCF_rho_one_le_of_not_isDisplayed hN hθ hq hT₃
    (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hT₁).1.trans (mem_treesOn.1 hT₃))) hnd
  have h₂ := nmscCF_rho_one_le_of_not_isDisplayed hN hθ hq hT₃
    (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hT₂).1.trans (mem_treesOn.1 hT₃))) hnd
  exact absurd hlt (not_lt.2 (le_min h₁ h₂))

/-- **Proposition 12, class 1** (`ext:ane2024-proposition12`), with Definition 2: "a 4-taxon binary metric network `N` of class 1 is
anomalous if `P(T₁|N) < 1/3`". A network displaying only `T₁` on the four taxa has `1/3 ≤ P(T₁)` at `ρ = 1`. -/
theorem proposition12_class1 (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {q : Finset X} (hq : q.card = 4)
    {T₁ : QuartetTree X} (hT₁ : T₁ ∈ treesOn q) (hone : ∀ r ∈ treesOn q, IsDisplayed N r → r = T₁) :
    1 / 3 ≤ nmscCF N θ 1 T₁ := by
  have hle : ∀ r ∈ treesOn q, nmscCF N θ 1 r ≤ nmscCF N θ 1 T₁ := fun r hr => by
    by_cases hrT : r = T₁
    · rw [hrT]
    · exact nmscCF_rho_one_le_of_not_isDisplayed hN hθ hq hr hT₁ fun hd => hrT (hone r hr hd)
  have hsum := NMSC.sum_nmscCF_weak (θ := θ) (ρ := 1) hN hθ.isNormalized zero_le_one hq
  have hbound : ∑ r ∈ treesOn q, nmscCF N θ 1 r ≤ ∑ _r ∈ treesOn q, nmscCF N θ 1 T₁ := sum_le_sum hle
  rw [hsum, sum_const, card_treesOn hq] at hbound
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hbound
  linarith

end External.AneEtAl2024
