module

public import AllmanEtAl2023.Theorem1
public import AllmanEtAl2023.NetworkNkMixture
public import AllmanEtAl2023.GenericDense
public import AllmanEtAl2023.Bridges

/-!
# Allman, Baños, Mitchell, Rhodes 2023: Proposition 1

**The first part.** The proof cites "statement 1 of Theorem 1". That statement is for generic parameters and Proposition 1 is for all valid parameters, but generic parameters are dense
and `CF`s are continuous, so the citation is good: `proposition1` follows it, with `ForGenericParams.eq_zero_of_continuous`.

**The converse.** "Arises" means: there are a network of the sort described and valid numerical parameters of Definition 3 at which the `CF` is the triple. The proof gives more: the
network is `𝒩(k)⁺` for all sufficiently large `k`, with lengths `metricNk k ε M` for some `ε, M > 0`, and hybridization parameters `1/2` (`NetworkNk.exists_params`). The proof is the paper's:

* `α` is the probability that the lineages of `a`, `b` are on different edges at height `1 + (k + 1)ε`, the union of `k` disjoint events of probabilities `(p/2)^ℓ` (`stageMass_divLevel`, `divAt_iff_exists_splitAt`, `eq_of_splitAt_of_splitAt`, `fullMass_divAt`,
  in `AllmanEtAl2023.NetworkNkCF` and `AllmanEtAl2023.NetworkNkMixture`).
* `CF_abcd = α CF₁ + (1 - α) CF₂` for the conditional masses `cfOne`, `cfTwo` (`nmscCF_eq_mixture`).
* `α CF₁` is the mean of the concordance factors on the species trees `(((c, a), b), d)` and `(((c, b), a), d)`, of equal probability, with edge `mM` (`mul_cfOne_eq_species`, `alpha_eq_sum_leafProb`, `fullMass_arrAt`, in `AllmanEtAl2023.NetworkNkSpecies` and
  `AllmanEtAl2023.NetworkNkMixture`). So `CF₁` is near `(0, 1/2, 1/2)` (`cfOne_first_le`, `cfOne_second_eq_third`, `cfOne_second_bounds`), and the entries of `CF₂` are bounded (`cfTwo_le_one`).
* `cf_first_le` is the bound that gives; then `ε ≫ 0` gives a first entry near 1, and the intermediate value theorem, on the segment of `ε` at fixed `k` and `M`, all those between.

There is no departure from the paper in this proof.

**In the source.**
* "Note that by Theorem 1, `CF_abcd` is strictly `(ab|cd)`-cut for `ε > 0`" is wrong as a claim on all `ε > 0`, since Theorem 1 is generic and the converse itself makes `(1/3, 1/3, 1/3)` arise
  (`NetworkNk.exists_not_isStrictlyCutAtFirst`). The sentence isn't used.
* The letter `p` is both `exp (-ε)` and the entry of the triple; the last paragraph writes `(q, p, p)`, `q + 2p = 1`, for the triple that the statement writes `(p, q, q)`.
* The PMC manuscript prints the lengths of the pendant edges as "`1, 1, 1 + (k + 1)ε + (2^k - 1)M`": three lengths for four edges. See `AllmanEtAl2023.NetworkNk`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC AllmanEtAl2023.NetworkNk Filter Topology
open scoped Classical

universe u

namespace AllmanEtAl2023

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ### The first part -/

section FirstPart

variable {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X}

/-- The entries of `CF_abcd` sum to one. -/
theorem sum_cfTriple (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsWeakMetric θ) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    (cfTriple N θ a b c d h).1 + (cfTriple N θ a b c d h).2.1 + (cfTriple N θ a b c d h).2.2 = 1 :=
  sum_cfTriple_weak hN hθ.isNormalized h

/-- **Proposition 1** (`a:prop:Nk`). Let `𝒩⁺` be a 4-taxon rooted binary phylogenetic network whose reduced tree of blobs has quartet
topology `ab|cd`. Then under the NMSC the `CF` is `ab|cd`-cut, with `CF_abcd = (CF_{ab|cd}, CF_{ac|bd}, CF_{ad|bc}) = (p, q, q)`,
where `0 < p, q < 1`, `p + 2q = 1`. Conversely (`proposition1_converse`), every such triple `(p, q, q)` arises as the `CF` from
such a network.

The proof cites statement 1 of Theorem 1, which holds for generic parameters; generic parameters are dense and `CF`s continuous. -/
theorem proposition1 (hN : IsBinaryNetwork N) (hcard : Fintype.card X = 4) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4)
    (hT : (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d) {θ : MetricData E}
    (hθ : N.IsMetric θ) :
    ∃ p q : ℝ, cfTriple N θ a b c d h = (p, q, q) ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧ p + 2 * q = 1 := by
  have hP := hN.isPhylogenetic
  have hE : Nonempty E := nonempty_arcs hP
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  -- statement 1 of Theorem 1, for generic parameters, and for all by density and continuity
  let Φ : MetricData E → ℝ := fun θ' =>
    nmscCF N θ' 0 (quartetTree a c b d (card_acbd h)) - nmscCF N θ' 0 (quartetTree a d b c (card_adbc h))
  have hgen : ForGenericParams N fun θ' => Φ θ' = 0 := by
    refine IsGenericNull.mono (theorem1 hN hcard) fun θ' hθ' => ⟨hθ'.1, fun hne => hθ'.2 ?_⟩
    exact sub_eq_zero.2 ((hne a b c d h).1.1 hT).2
  have hcont : ∀ d' : V → E, Continuous fun x : (E → ℝ) × (E → ℝ) => Φ (coordMetric N d' x.1 x.2) := fun d' =>
    (continuousOn_univ.1 (analyticOnNhd_nmscCF_coordMetric N d' 0 _).continuousOn).sub
      (continuousOn_univ.1 (analyticOnNhd_nmscCF_coordMetric N d' 0 _).continuousOn)
  have hcut : Φ θ = 0 := ForGenericParams.eq_zero_of_continuous hE hcont hgen hθ
  have hsum := sum_cfTriple hP hθ.isWeakMetric (a := a) (b := b) (c := c) (d := d) h
  have hp : 0 < (cfTriple N θ a b c d h).1 := nmscCF_pos hP hθ hρ _
  have hq : 0 < (cfTriple N θ a b c d h).2.1 := nmscCF_pos hP hθ hρ _
  have he : (cfTriple N θ a b c d h).2.1 = (cfTriple N θ a b c d h).2.2 := sub_eq_zero.1 hcut
  refine ⟨(cfTriple N θ a b c d h).1, (cfTriple N θ a b c d h).2.1, ?_, hp, by linarith, hq, by linarith, by linarith⟩
  exact Prod.ext rfl (Prod.ext rfl he.symm)

end FirstPart

/-! ### The networks `𝒩(k)⁺` -/

namespace NetworkNk

/-- `𝒩(k)⁺` is a network of Definition 1. -/
theorem isBinaryNetwork_networkNk (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) : IsBinaryNetwork (networkNk k a b c d) :=
  isBinaryNetwork_iff.2 ⟨isPhylogenetic_networkNk h hX, isBinary_networkNk⟩

/-- `T_rd(𝒩(k)⁻)` has the quartet tree topology `ab|cd`: "edges lead from the root to the taxon `d` and to a 3-blob. The other two
edges incident to the 3-blob lead to `c`, and to a cherry of `a, b`". On four taxa the topology is displayed exactly when a cut edge has the split: the proof needs only the stem,
of the arcs of that sentence (`displays_treeOfBlobs_networkNk`). -/
theorem hasQuartetTopology_networkNk (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) :
    (Trd (isBinaryNetwork_networkNk k h hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d := by
  rw [Bridges.hasQuartetTopology_iff_displays _ hX h, Bridges.splits_Trd]
  exact displays_treeOfBlobs_networkNk h

/-- "Taking `ε` close to `0` ensures `p` is as close to 1 as desired. Then choosing `k` sufficiently large, the probability `α` can be made as close to `p / (2 - p)` as desired, and hence arbitrarily close to 1." -/
theorem exists_alpha_gt {δ : ℝ} (hδ : 0 < δ) : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, 1 - δ < alpha k ε := by
  have hc : ContinuousAt (fun ε : ℝ => Real.exp (-ε) / 2 * (1 - Real.exp (-ε) / 2)⁻¹) 0 := by
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.inv₀ (by fun_prop) ?_)
    norm_num
  have hval : (fun ε : ℝ => Real.exp (-ε) / 2 * (1 - Real.exp (-ε) / 2)⁻¹) 0 = 1 := by
    norm_num
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 - δ < Real.exp (-ε) / 2 * (1 - Real.exp (-ε) / 2)⁻¹ :=
    hc.eventually (lt_mem_nhds (by rw [hval]; linarith))
  obtain ⟨ε₁, hε₁, hε₁0⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    1 - δ < Real.exp (-ε) / 2 * (1 - Real.exp (-ε) / 2)⁻¹ ∧ ε ∈ Set.Ioi 0).exists
  have hε₁pos : (0 : ℝ) < ε₁ := hε₁0
  have hr0 : 0 ≤ Real.exp (-ε₁) / 2 := by positivity
  have hr1 : Real.exp (-ε₁) / 2 < 1 := by
    have : Real.exp (-ε₁) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hlim : Tendsto (fun k => alpha k ε₁) atTop (𝓝 (Real.exp (-ε₁) / 2 * (1 - Real.exp (-ε₁) / 2)⁻¹)) := by
    simp only [alpha_eq_mul_sum_range]
    exact (hasSum_geometric_of_lt_one hr0 hr1).tendsto_sum_nat.const_mul _
  exact ⟨ε₁, hε₁pos, hlim.eventually (lt_mem_nhds hε₁)⟩

/-- "We can make `CF_abcd` as close to `(0, 1/2, 1/2)` as desired by choices of `ε ≈ 0` and `k, M ≫ 0`", in the form of the bound behind it: `CF_{ab|cd} = α CF₁ + (1 - α) CF₂` (`nmscCF_eq_mixture`), in which the first entry of `CF₂` is at most 1
(`cfTwo_le_one`), and that of `CF₁` is at most `exp (-M)` (`cfOne_first_le`), from its species trees. -/
theorem cf_first_le (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 ≤
      (1 - alpha k ε) + Real.exp (-M) :=
  nmscCF_first_le_of_mixture h hX hε hM

/-- "We can make `CF_abcd` as close to `(0, 1/2, 1/2)` as desired by choices of `ε ≈ 0` and `k, M ≫ 0`": for `ε` small, all large `k`, and `M` large. -/
theorem cf_near_zero_half {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ∀ᶠ M in atTop, 0 < M ∧
      (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 < δ ∧
        |(cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).2.1 - 1 / 2| < δ ∧
        |(cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).2.2 - 1 / 2| < δ := by
  obtain ⟨ε, hε, hk⟩ := exists_alpha_gt (δ := δ / 2) (by positivity)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hk] with k hα
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by positivity : 0 < δ / 2)), eventually_gt_atTop 0] with M hM hMpos
  obtain ⟨p, q, heq, hp, -, hq, -, hsum⟩ := proposition1 (isBinaryNetwork_networkNk k h hX) hX h (hasQuartetTopology_networkNk k h hX)
    (isMetric_metricNk h hX hε hMpos)
  have hb := cf_first_le k h hX hε hMpos
  rw [heq] at hb ⊢
  simp only at hb ⊢
  have hp' : p < δ := by linarith
  have hq' : |q - 1 / 2| < δ := by
    rw [abs_lt]
    constructor <;> linarith
  exact ⟨hMpos, hp', hq', hq'⟩

/-- "We could instead take `ε ≫ 0`, making the probability of coalescence of `a, b` on the edge above the `{a, b}` cherry as close to
1 as we like, so that `CF_abcd` is arbitrarily close to `(1, 0, 0)`." -/
theorem one_sub_exp_le_cf_first (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    1 - Real.exp (-ε) ≤ (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 :=
  one_sub_exp_le_nmscCF (e := Edge.stem) (isPhylogenetic_networkNk h hX)
    (isMetric_metricNk h hX hε hM).isWeakMetric ⟨le_rfl, zero_le_one⟩
    (isDeletion_empty (isPhylogenetic_networkNk h hX)) (fun _ hf => absurd hf (Set.notMem_empty _)) (splitOffAt_stem h)

/-- `CF_{ab|cd}` is continuous in `ε`. -/
theorem continuous_cf_first (k : ℕ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (M : ℝ) :
    Continuous fun ε => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 := by
  refine continuousOn_univ.1 (AnalyticOnNhd.continuousOn (analyticOnNhd_nmscCF (networkNk k a b c d)
    (θ := fun ε : ℝ => metricNk k ε M) 0 (fun e => ?_) (fun e => analyticOnNhd_const) _))
  have haff : ∀ u v : ℝ, AnalyticOnNhd ℝ (fun x : ℝ => u + v * x) Set.univ := fun u v =>
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  cases e with
  | rootTaxon =>
    refine (haff (2 + (2 ^ k - 1) * M) (k + 1)).congr isOpen_univ fun x _ => ?_
    simp only [metricNk]
    ring
  | rootTop => exact analyticOnNhd_const
  | step t => exact analyticOnNhd_const
  | bottomTaxon => exact haff 1 (k + 1)
  | tree m =>
    simp only [metricNk]
    split_ifs
    · exact analyticOnNhd_id
    · refine (haff (((m.1 + 2 - 2 ^ k : ℕ) : ℝ) * M) 1).congr isOpen_univ fun x _ => ?_
      ring
  | stem => exact analyticOnNhd_id
  | cherryLeft => exact analyticOnNhd_const
  | cherryRight => exact analyticOnNhd_const

/-- The proof of the converse of Proposition 1: "a triple `(p, q, q)` arises as a `CF` on `𝒩(k)⁺` for sufficiently large `k` and
certain numerical parameters". -/
theorem exists_params {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + 2 * q = 1) :
    ∀ᶠ k in atTop, ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h = (p, q, q) := by
  have hp1 : 0 < 1 - p := by linarith
  obtain ⟨ε₁, hε₁pos, hk⟩ := exists_alpha_gt (δ := p / 2) (by positivity)
  -- "by choosing `M` large enough"
  obtain ⟨M, hM, hMpos⟩ := ((Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by positivity : 0 < p / 2))).and
    (eventually_gt_atTop 0)).exists
  -- "we could instead take `ε ≫ 0`"
  obtain ⟨ε₂, hε₂, hε₂₁⟩ := ((Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hp1)).and
    (eventually_ge_atTop ε₁)).exists
  filter_upwards [hk] with k hk
  have hF₁ : (cfTriple (networkNk k a b c d) (metricNk k ε₁ M) a b c d h).1 ≤ p := by
    have := cf_first_le k h hX hε₁pos hMpos
    linarith
  have hF₂ : p ≤ (cfTriple (networkNk k a b c d) (metricNk k ε₂ M) a b c d h).1 := by
    have := one_sub_exp_le_cf_first k h hX (lt_of_lt_of_le hε₁pos hε₂₁) hMpos
    linarith
  -- "by connectedness of the numerical parameter space, all intermediate points between the ones we found arise"
  obtain ⟨ε, ⟨hε1, -⟩, hFε⟩ := intermediate_value_Icc hε₂₁ (continuous_cf_first k h M).continuousOn ⟨hF₁, hF₂⟩
  have hεpos : 0 < ε := lt_of_lt_of_le hε₁pos hε1
  refine ⟨ε, M, hεpos, hMpos, ?_⟩
  -- "Since `CF_abcd` lies on the line of points of the form `(q, p, p)`, `q + 2p = 1`"
  obtain ⟨p', q', heq, -, -, -, -, hsum⟩ := proposition1 (isBinaryNetwork_networkNk k h hX) hX h
    (hasQuartetTopology_networkNk k h hX) (isMetric_metricNk h hX hεpos hMpos)
  have hp' : p' = p := by
    have h1 : (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 = p := hFε
    rw [heq] at h1
    exact h1
  have hq' : q' = q := by
    rw [hp'] at hsum
    linarith
  rw [heq, hp', hq']

/-- "Note that by Theorem 1, `CF_abcd` is strictly `(ab|cd)`-cut for `ε > 0`" fails as a claim on all `ε > 0`: `(1/3, 1/3, 1/3)` arises at some `ε > 0`. The sentence isn't used in the paper. -/
theorem exists_not_isStrictlyCutAtFirst {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) :
    ∃ (k : ℕ) (ε M : ℝ), 0 < ε ∧ 0 < M ∧
      ¬ IsStrictlyCutAtFirst (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h) := by
  obtain ⟨k, ε, M, hε, hM, heq⟩ := (exists_params h hX (p := 1 / 3) (q := 1 / 3) (by norm_num) (by norm_num) (by norm_num)).exists
  refine ⟨k, ε, M, hε, hM, fun hs => hs.1 ?_⟩
  rw [heq]

end NetworkNk

/-- **Proposition 1, the converse** (`a:prop:Nk`): every triple `(p, q, q)` with `0 < p, q < 1`, `p + 2q = 1`, arises as the `CF` from
a 4-taxon rooted binary phylogenetic network whose reduced tree of blobs has quartet topology `ab|cd`. -/
theorem proposition1_converse (hcard : Fintype.card X = 4) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4)
    {p q : ℝ} (hp : 0 < p) (_hp1 : p < 1) (hq : 0 < q) (_hq1 : q < 1) (hpq : p + 2 * q = 1) :
    ∃ (V : Type u) (E : Type) (_ : Fintype V) (_ : Fintype E) (N : RootedNetwork V E X) (hN : IsBinaryNetwork N)
      (θ : MetricData E), N.IsMetric θ ∧
        (Trd hN (nontrivial_of_card_four hcard)).HasQuartetTopology a b c d ∧
        cfTriple N θ a b c d h = (p, q, q) := by
  obtain ⟨k, ε, M, hε, hM, heq⟩ := (NetworkNk.exists_params h hcard hp hq hpq).exists
  exact ⟨Vertex k X, Edge k, inferInstance, inferInstance, networkNk k a b c d, NetworkNk.isBinaryNetwork_networkNk k h hcard,
    metricNk k ε M, NetworkNk.isMetric_metricNk h hcard hε hM, NetworkNk.hasQuartetTopology_networkNk k h hcard, heq⟩

end AllmanEtAl2023
