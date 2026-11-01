module

public import AllmanEtAl2023.Proposition1
public import AllmanEtAl2023.NetworkNkExact

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the distance between blobs is not identifiable

"For example, on the 4-taxon network in Fig. 6 if the length of the edge between the blobs is held fixed but `k` or `M` varied, the `CF` varies over a line segment. This segment overlaps a similarly constructed segment
of `CF`s for a nearby value `ε′ ≈ ε`. Thus the distance between blobs cannot be identified in this 4-taxon case." (Section 5 of the PMC manuscript.) The arXiv version: "This segment intersects a similar segment for a nearby value of `ε`."

The edge between the blobs of `𝒩(k)⁺` is the stem, of length `ε`. On one topological network `𝒩(k)⁺`, so with one tree of blobs, of topology `ab|cd`, for every `k ≥ 1` and every `ε > 0`:

* the first entry of the `CF` is continuous in `M` (`continuous_cf_first_M`), and the `CF` is on the line `(v, (1 - v)/2, (1 - v)/2)` (`cfTriple_eq_of_first`). This is the segment (`isPreconnected_cf_first`).
* its limits at `M → 0⁺` and `M → ∞` are `cfZero k ε` and `cfInfty k ε`, and differ (`NetworkNk.cfInfty_lt_cfZero`), by the exact formula of `AllmanEtAl2023.NetworkNkExact`. So every value between them arises (`exists_M_of_value`).
* the limits are continuous in `ε`, so the segments of `ε₀` and of all `ε′` near it share a nondegenerate segment: `blobDistance_not_identifiable`.

"`k` or `M` varied" is loose, since `k` is discrete: with `M` fixed, `k` gives only points. Two readings hold: `M` varied at a fixed `k`, as above, and `k` and `M` varied together: `isPreconnected_iUnion_cf_first`, the union of the segments of all `k ≥ 1` at one `ε` is a segment.

`cfTriple_tree`, `cf_tree_range`: on a species tree, what the paper cites before Proposition 1.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset Filter Topology AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.InPassing

open AllmanEtAl2023.NetworkNk

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} {a b c d : X}

/-! ### The segment -/

section Segment

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)

/-- `CF_{ab|cd}` is continuous in `M`. -/
theorem continuous_cf_first_M (k : ℕ) (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) (ε : ℝ) :
    Continuous fun M => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1 := by
  refine continuousOn_univ.1 (AnalyticOnNhd.continuousOn (analyticOnNhd_nmscCF (networkNk k a b c d)
    (θ := fun M : ℝ => metricNk k ε M) 0 (fun e => ?_) (fun e => analyticOnNhd_const) _))
  have haff : ∀ u v : ℝ, AnalyticOnNhd ℝ (fun x : ℝ => u + v * x) Set.univ := fun u v =>
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)
  cases e with
  | rootTaxon =>
    refine (haff (2 + (k + 1) * ε) (2 ^ k - 1)).congr isOpen_univ fun x _ => ?_
    simp only [metricNk]
  | rootTop => exact analyticOnNhd_const
  | step t => exact analyticOnNhd_id
  | bottomTaxon => exact analyticOnNhd_const
  | tree m =>
    simp only [metricNk]
    split_ifs
    · exact analyticOnNhd_const
    · exact haff ε _
  | stem => exact analyticOnNhd_const
  | cherryLeft => exact analyticOnNhd_const
  | cherryRight => exact analyticOnNhd_const

/-- **"The `CF` varies over a line segment"**: as `M` varies at fixed `k`, `ε`, the first entries form an interval, and by Proposition 1 the `CF`s are on the line `(v, (1 - v)/2, (1 - v)/2)`. -/
theorem isPreconnected_cf_first (k : ℕ) (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) (ε : ℝ) :
    IsPreconnected ((fun M => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d h).1) '' Set.Ioi 0) :=
  isPreconnected_Ioi.image _ (continuous_cf_first_M k a b c d h ε).continuousOn

include hd hX in
/-- A `CF` of `𝒩(k)⁺` with first entry `v` is on the line. -/
theorem cfTriple_eq_of_first {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) {v : ℝ}
    (hv : (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd).1 = v) :
    cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd = (v, (1 - v) / 2, (1 - v) / 2) := by
  obtain ⟨p', q', heq, -, -, -, -, hsum⟩ := proposition1 (isBinaryNetwork_networkNk k hd hX) hX hd
    (hasQuartetTopology_networkNk k hd hX) (isMetric_metricNk hd hX hε hM)
  have hp' : p' = v := by
    rw [heq] at hv
    exact hv
  have hq' : q' = (1 - v) / 2 := by
    rw [hp'] at hsum
    linarith
  rw [heq, hp', hq']

include hd hX in
/-- **The segment of `ε`**: every value strictly between the limits of the first entry at `M → ∞` and at `M → 0⁺` is the first entry of a `CF` of `𝒩(k)⁺` at `ε`, for some `M > 0`. -/
theorem exists_M_of_value (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) {v : ℝ} (h1 : cfInfty k ε < v) (h2 : v < cfZero k ε) :
    ∃ M : ℝ, 0 < M ∧ cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd = (v, (1 - v) / 2, (1 - v) / 2) := by
  obtain ⟨M₁, hM₁, hM₁pos⟩ := ((tendsto_cf_first_zero (a := a) (b := b) (c := c) (d := d) hd hX hε hk).eventually (lt_mem_nhds h2) |>.and self_mem_nhdsWithin).exists
  obtain ⟨M₂, hM₂, hM₂₁⟩ := ((tendsto_cf_first_atTop (a := a) (b := b) (c := c) (d := d) hd hX hε hk).eventually (gt_mem_nhds h1) |>.and (eventually_gt_atTop M₁)).exists
  obtain ⟨M, ⟨hM0, -⟩, hFM⟩ := intermediate_value_Icc' hM₂₁.le (continuous_cf_first_M k a b c d hd ε).continuousOn ⟨hM₂.le, hM₁.le⟩
  have hMpos : 0 < M := lt_of_lt_of_le hM₁pos hM0
  exact ⟨M, hMpos, cfTriple_eq_of_first hd hX hε hMpos hFM⟩

end Segment

omit [Fintype X] [DecidableEq X] in
theorem continuous_alpha (k : ℕ) : Continuous fun ε => alpha k ε := by
  unfold alpha
  fun_prop

omit [Fintype X] [DecidableEq X] in
theorem continuous_cfZero (k : ℕ) : Continuous fun ε => cfZero k ε := by
  unfold cfZero
  have := continuous_alpha k
  fun_prop

omit [Fintype X] [DecidableEq X] in
theorem continuous_cfInfty (k : ℕ) : Continuous fun ε => cfInfty k ε := by
  unfold cfInfty
  have := continuous_alpha k
  fun_prop

/-- **"Thus the distance between blobs cannot be identified in this 4-taxon case"** (`a:claim:blob-distance`, in Section 5). On one topological network `𝒩(k)⁺`, for every `k ≥ 1`, whose tree of blobs has the topology `ab|cd`, the edge between the blobs being the stem of
length `ε`: for every `ε₀ > 0` and for all `ε′` near `ε₀`, "this segment overlaps a similarly constructed segment of `CF`s": a nondegenerate segment `[q₁, q₂]` of first entries arises at `ε₀` and at `ε′`. Here `M` varies; see the module docstring on the
quantifiers. -/
theorem blobDistance_not_identifiable {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {k : ℕ} (hk : 1 ≤ k) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    (Trd (isBinaryNetwork_networkNk k h hX) (nontrivial_of_card_four hX)).HasQuartetTopology a b c d ∧
      ∃ q₁ q₂ : ℝ, q₁ < q₂ ∧ ∀ᶠ ε' in 𝓝 ε₀, 0 < ε' ∧ ∀ v ∈ Set.Icc q₁ q₂, ∃ M M' : ℝ, 0 < M ∧ 0 < M' ∧
        cfTriple (networkNk k a b c d) (metricNk k ε₀ M) a b c d h = (v, (1 - v) / 2, (1 - v) / 2) ∧
        cfTriple (networkNk k a b c d) (metricNk k ε' M') a b c d h = (v, (1 - v) / 2, (1 - v) / 2) := by
  refine ⟨hasQuartetTopology_networkNk k h hX, ?_⟩
  have hgap := cfInfty_lt_cfZero hk hε₀
  set u := cfInfty k ε₀ with hu
  set w := cfZero k ε₀ with hw
  refine ⟨u + (w - u) / 3, u + 2 * (w - u) / 3, by linarith, ?_⟩
  have hnear₁ : ∀ᶠ ε' in 𝓝 ε₀, cfInfty k ε' < u + (w - u) / 3 :=
    (continuous_cfInfty k).continuousAt.eventually (gt_mem_nhds (by linarith))
  have hnear₂ : ∀ᶠ ε' in 𝓝 ε₀, u + 2 * (w - u) / 3 < cfZero k ε' :=
    (continuous_cfZero k).continuousAt.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hnear₁, hnear₂, lt_mem_nhds hε₀] with ε' h₁ h₂ hε'pos
  refine ⟨hε'pos, fun v hv => ?_⟩
  obtain ⟨M, hM, heq⟩ := exists_M_of_value (a := a) (b := b) (c := c) (d := d) h hX hk hε₀ (v := v) (by linarith [hv.1]) (by linarith [hv.2])
  obtain ⟨M', hM', heq'⟩ := exists_M_of_value (a := a) (b := b) (c := c) (d := d) h hX hk hε'pos (v := v) (by linarith [hv.1]) (by linarith [hv.2])
  exact ⟨M, M', hM, hM', heq, heq'⟩

/-! ### `k` and `M` varied together -/

section Union

variable {ε : ℝ}

omit [Fintype X] [DecidableEq X] in
theorem alpha_succ (k : ℕ) (ε : ℝ) : alpha (k + 1) ε = alpha k ε + (Real.exp (-ε) / 2) ^ (k + 1) := by
  unfold alpha
  rw [Finset.sum_Icc_succ_top (by omega)]

omit [Fintype X] [DecidableEq X] in
/-- The upper end of the segment of `k` is above the lower end of that of `k + 1`. -/
theorem cfInfty_succ_lt_cfZero (hk : 1 ≤ k) (hε : 0 < ε) : cfInfty (k + 1) ε < cfZero k ε := by
  have hp1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set x := Real.exp (-ε) / 2 with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x < 1 := by rw [hx]; linarith
  have hα : x ^ 1 ≤ alpha k ε := pow_le_alpha le_rfl hk ε
  have hpow : x ^ (k + 1) ≤ x ^ 1 := pow_le_pow_of_le_one hx0.le hx1.le (by omega)
  have hp : Real.exp (-ε) = 2 * x := by rw [hx]; ring
  have hq : 0 < Real.exp (-ε) * (Real.exp (-ε) / 4) ^ (k + 1) := by positivity
  have hsucc : Real.exp (-ε) * x ^ k = 2 * x ^ (k + 1) := by
    rw [hp, pow_succ]
    ring
  unfold cfZero cfInfty
  rw [alpha_succ, ← hx, hsucc]
  linarith

omit [Fintype X] [DecidableEq X] in
/-- The upper end of the segment of `k + 1` is above the lower end of that of `k`. -/
theorem cfInfty_lt_cfZero_succ (hk : 1 ≤ k) (hε : 0 < ε) : cfInfty k ε < cfZero (k + 1) ε := by
  have hp1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hp0 : 0 < Real.exp (-ε) := Real.exp_pos _
  set x := Real.exp (-ε) / 2 with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x < 1 / 2 := by rw [hx]; linarith
  have hp : Real.exp (-ε) = 2 * x := by rw [hx]; ring
  unfold cfZero cfInfty
  rw [alpha_succ, ← hx]
  obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
  · rw [alpha_one, ← hx, hp, show 2 * x / 4 = x / 2 by ring]
    have h4 : 4 * x * x < 1 := by nlinarith
    have : 0 < x * (1 - 4 * x * x) := mul_pos hx0 (by linarith)
    simp only [pow_succ, pow_zero, one_mul]
    nlinarith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hα : x ^ (j + 1) + x ^ (j + 1 + 1) ≤ alpha (j + 2) ε := pow_add_pow_le_alpha (by omega) le_rfl ε
    have hy : 0 < x ^ (j + 1) := by positivity
    have hq : 0 < Real.exp (-ε) * (Real.exp (-ε) / 4) ^ (j + 2) := by positivity
    have h5 : Real.exp (-ε) * x ^ (j + 2 + 1) = x ^ (j + 1) * (2 * x * (x * x)) := by
      rw [hp]
      ring
    have h6 : x ^ (j + 2 + 1) = x ^ (j + 1) * (x * x) := by ring
    have h7 : x ^ (j + 1 + 1) = x ^ (j + 1) * x := by ring
    rw [h5, h6]
    rw [h7] at hα
    have h8 : 2 * x * (x * x) < x * x := by nlinarith [mul_pos hx0 hx0]
    have h9 : x * x < x / 2 := by nlinarith
    nlinarith [mul_pos hy hx0, mul_lt_mul_of_pos_left h8 hy, mul_lt_mul_of_pos_left h9 hy]

/-- **"`k` or `M` varied"**, with `k` and `M` varied together: the first entries of the `CF`s of the networks `𝒩(k)⁺`, `k ≥ 1`, at one `ε`, form a segment. -/
theorem isPreconnected_iUnion_cf_first {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) (hε : 0 < ε) :
    IsPreconnected (⋃ k : ℕ, (fun M => (cfTriple (networkNk (k + 1) a b c d) (metricNk (k + 1) ε M) a b c d h).1) '' Set.Ioi 0) := by
  refine IsPreconnected.iUnion_of_chain (fun k => isPreconnected_cf_first (k + 1) a b c d h ε) fun k => ?_
  have hk : 1 ≤ k + 1 := by omega
  rw [Order.succ_eq_add_one]
  have h1 := cfInfty_lt_cfZero hk hε
  have h2 := cfInfty_lt_cfZero (k := k + 1 + 1) (by omega) hε
  have h3 := cfInfty_succ_lt_cfZero hk hε
  have h4 := cfInfty_lt_cfZero_succ hk hε
  obtain ⟨v, hv₁, hv₂⟩ := exists_between (max_lt (lt_min h1 h4) (lt_min h3 h2))
  have hv₃ := lt_of_le_of_lt (le_max_left _ _) hv₁
  have hv₄ := lt_of_le_of_lt (le_max_right _ _) hv₁
  obtain ⟨M, hM, heq⟩ := exists_M_of_value (a := a) (b := b) (c := c) (d := d) h hX hk hε (v := v) hv₃ (lt_of_lt_of_le hv₂ (min_le_left _ _))
  obtain ⟨M', hM', heq'⟩ := exists_M_of_value (a := a) (b := b) (c := c) (d := d) h hX (k := k + 1 + 1) (by omega) hε (v := v) hv₄ (lt_of_lt_of_le hv₂ (min_le_right _ _))
  exact ⟨v, ⟨M, hM, by simp only [heq]⟩, ⟨M', hM', by simp only [heq']⟩⟩

end Union

/-! ### On a species tree -/

section Tree

/-- **The `CF` on the species tree `(((a, b), c), d)`**: "two of the three entries of `CF_abcd` must be equal, with the third no smaller", as Allman et al. (2011) show of trees (after Definition 14). -/
theorem cfTriple_tree {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    cfTriple (networkNk 0 a b c d) (treeMetric L₁ L₂) a b c d h = (1 - 2 / 3 * Real.exp (-L₁), Real.exp (-L₁) / 3, Real.exp (-L₁) / 3) := by
  obtain ⟨p', q', heq, -, -, -, -, hsum⟩ := proposition1 (isBinaryNetwork_networkNk 0 h hX) hX h
    (hasQuartetTopology_networkNk 0 h hX) (isMetric_treeMetric h hX h₁ h₂)
  have hF : (cfTriple (networkNk 0 a b c d) (treeMetric L₁ L₂) a b c d h).1 = 1 - 2 / 3 * Real.exp (-L₁) := nmscCF_tree_first h hX h₁ h₂
  rw [heq] at hF
  have hp : p' = 1 - 2 / 3 * Real.exp (-L₁) := hF
  have hq : q' = Real.exp (-L₁) / 3 := by
    rw [hp] at hsum
    linarith
  rw [heq, hp, hq]

/-- **"If `𝒩⁺` is a resolved tree, then Allman et al. (2011) showed `CF_{ab|cd}` may take on any value in the interval `(1/3, 1)`"** (`a:claim:tree-range`, before Proposition 1): on the species tree `(((a, b), c), d)`, all these values arise, and no others. -/
theorem cf_tree_range {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {v : ℝ} :
    (1 / 3 < v ∧ v < 1) ↔ ∃ L₁ : ℝ, 0 < L₁ ∧ (cfTriple (networkNk 0 a b c d) (treeMetric L₁ 1) a b c d h).1 = v := by
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < 3 / 2 * (1 - v) := by linarith
    have hlt : 3 / 2 * (1 - v) < 1 := by linarith
    refine ⟨-Real.log (3 / 2 * (1 - v)), by linarith [Real.log_neg hpos hlt], ?_⟩
    have hL : 0 < -Real.log (3 / 2 * (1 - v)) := by linarith [Real.log_neg hpos hlt]
    rw [cfTriple_tree h hX hL one_pos, neg_neg, Real.exp_log hpos]
    ring
  · rintro ⟨L₁, hL, rfl⟩
    rw [cfTriple_tree h hX hL one_pos]
    have h0 := Real.exp_pos (-L₁)
    have h1 : Real.exp (-L₁) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    constructor
    · simp only
      linarith
    · simp only
      linarith

end Tree

end AllmanEtAl2023.InPassing
