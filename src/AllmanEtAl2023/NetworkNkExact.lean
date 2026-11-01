module

public import AllmanEtAl2023.NetworkNkMixture

/-!
# Allman, Baños, Mitchell, Rhodes 2023: the first entry of `CF_abcd` on `𝒩(k)⁺`, exactly

The remark at the end of Section 5 says that on `𝒩(k)⁺`, as `M` varies, "the `CF` varies over a line segment", and that this segment overlaps the segment of a nearby `ε′`. For that the proof of Proposition 1 needs only that `CF_{ab|cd}` is
small for large `M` and small `ε`, and the bound `CF_{ab|cd} ≤ (1 - α) + exp (-M)` isn't enough: for `k = 1` it lies above the value at `M → 0⁺` when `p > 1/2`, with `p = exp (-ε)`. This module computes the first entry exactly, for every `k ≥ 1`,
`ε > 0`, `M > 0`, following the event of the paper's proof: `CF_abcd = α CF₁ + (1 - α) CF₂`.

The complementary event of "different edges at height `1 + (k + 1) ε`" is that the lineages of `a` and `b` reach one 'leaf' `t` of the inverted subtree on one arc, coalesced or not.

* `sameH`, `sameG`, `sameVal`, `PhiS`: the probability that two lineages together on an arc stay together, not coalesced, up to the 'leaves'. `phiS_cherry`, `phiS_step`: its steps, as for `NetworkNk.PhiL`.
* `sum_fullMass_sameLeaf`: the probability that they arrive at one 'leaf' not coalesced is `p (p / 4) ^ k ∑_{t < 2 ^ k} exp (-t M)`.
* `arrivalsAt`, `pv_arrivalsAt`: the chain up the path, when one forest arrives on it.
* `value_same`: three lineages `a`, `b`, `c` on an arc give `ab|cd` with probability `1 / 3`, by their symmetry, and `value_coal`: `a`, `b` coalesced give `ab|cd`.
* `eventMass_not_divAt`: the first entry of `(1 - α) CF₂`, and `mul_cfOne_first`: that of `α CF₁`, from its species trees, on which the entry is `exp (-(j - i) M) / 3`.
* `cf_first_eq`: **the first entry of `CF_abcd`**.
* `cfZero`, `cfInfty`: the limits at `M → 0⁺` and `M → ∞`, with `tendsto_cf_first_zero`, `tendsto_cf_first_atTop` and `cfInfty_lt_cfZero`. For `k = 1` the difference is `p (1 - p) / 6` (`cfZero_sub_cfInfty_one`).
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset Filter Topology AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.NetworkNk

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} {a b c d : X}

/-! ### Two lineages staying together -/

/-- With `j` levels left below the 'leaves' of the inverted subtree, the probability that two lineages together on the arc entering the node `m`, past its length, stay together and not coalesced up to the 'leaves', times the part `exp (-t M)` of the length of the last arc beyond `ε`. -/
def sameH (k : ℕ) (ε M : ℝ) : ℕ → ℕ → ℝ
  | 0, m => Real.exp (-(((m - 2 ^ k : ℕ) : ℝ) * M))
  | j + 1, m => Real.exp (-ε) / 4 * (sameH k ε M j (2 * m) + sameH k ε M j (2 * m + 1))

/-- The probability that two lineages together at the node `m` of the inverted subtree stay together, not coalesced, up to the 'leaves'. -/
def sameG (k : ℕ) (ε M : ℝ) (m : ℕ) : ℝ := if 2 ^ k ≤ m then 1 else sameH k ε M (k - Nat.log 2 m) m

/-- The value of two lineages being together on an arc, past its length. -/
def sameVal (k : ℕ) (ε M : ℝ) : Edge k → ℝ
  | .stem => sameG k ε M 1
  | .tree m => sameG k ε M (m.1 + 2)
  | _ => 0

/-- **The closed form.** The 'leaves' above the node `m` with `j` levels left are the `2 ^ j m + s`, `s < 2 ^ j`. -/
theorem sameH_eq (k : ℕ) (ε M : ℝ) (j m : ℕ) (hm : 2 ^ k ≤ 2 ^ j * m) :
    sameH k ε M j m = (Real.exp (-ε) / 4) ^ j * ∑ s ∈ range (2 ^ j), Real.exp (-(((2 ^ j * m + s - 2 ^ k : ℕ) : ℝ) * M)) := by
  induction j generalizing m with
  | zero =>
    simp only [sameH, pow_zero, one_mul, range_one, sum_singleton, add_zero]
  | succ j ih =>
    have h1 : 2 ^ k ≤ 2 ^ j * (2 * m) := by
      rw [pow_succ] at hm
      calc 2 ^ k ≤ 2 ^ j * 2 * m := hm
        _ = 2 ^ j * (2 * m) := by ring
    have h2 : 2 ^ k ≤ 2 ^ j * (2 * m + 1) := h1.trans (Nat.mul_le_mul_left _ (by omega))
    rw [sameH, ih _ h1, ih _ h2, pow_succ (2 : ℕ) j, mul_comm (2 ^ j) 2, two_mul (2 ^ j), sum_range_add, pow_succ (Real.exp (-ε) / 4) j]
    have e1 : ∀ s, 2 ^ j * (2 * m) + s - 2 ^ k = (2 ^ j + 2 ^ j) * m + s - 2 ^ k := fun s => by
      congr 2
      ring
    have e2 : ∀ s, 2 ^ j * (2 * m + 1) + s - 2 ^ k = (2 ^ j + 2 ^ j) * m + (2 ^ j + s) - 2 ^ k := fun s => by
      rw [show 2 ^ j * (2 * m + 1) = (2 ^ j + 2 ^ j) * m + 2 ^ j by ring]
      congr 1
      omega
    simp only [e1, e2]
    ring

theorem sameH_one (k : ℕ) (ε M : ℝ) :
    sameH k ε M k 1 = (Real.exp (-ε) / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)) := by
  rw [sameH_eq k ε M k 1 (by simp)]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [mul_one, Nat.add_sub_cancel_left]

/-- At the 'root' of the inverted subtree. -/
theorem sameG_one (hk : 1 ≤ k) (ε M : ℝ) :
    sameG k ε M 1 = (Real.exp (-ε) / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [sameG, ite_eq_right (by omega), Nat.log_one_right, Nat.sub_zero, sameH_one]

omit [Fintype X] [DecidableEq X] in
theorem sameVal_outTree {ε M : ℝ} {m : ℕ} (h₁ : 1 ≤ m) (h₃ : m < 2 ^ (k + 1)) :
    sameVal k ε M (outTree m : Edge k) = sameG k ε M m := by
  by_cases hm : 2 ≤ m
  · rw [outTree_of_two_le hm h₃]
    simp only [sameVal]
    congr 1
    omega
  · obtain rfl : m = 1 := by omega
    rw [outTree_one]
    rfl

/-- The factor of an arc to a child of the node `m`. -/
theorem exp_length_mul_sameG {ε M : ℝ} {m m' : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (hm' : m' = 2 * m ∨ m' = 2 * m + 1)
    (i : Fin (2 ^ (k + 1) - 2)) (hi : i.1 + 2 = m') :
    Real.exp (-(metricNk k ε M).length (.tree i)) * sameG k ε M m' = Real.exp (-ε) * sameH k ε M (k - Nat.log 2 m - 1) m' := by
  have hlog : Nat.log 2 m' = Nat.log 2 m + 1 := by
    rcases hm' with rfl | rfl
    · rw [show 2 * m = 2 * m - 2 + 2 by omega]
      exact log_left h₁
    · rw [show 2 * m + 1 = 2 * m - 1 + 2 by omega]
      exact log_right h₁
  have hlt : Nat.log 2 m < k := Nat.log_lt_of_lt_pow (by omega) h₂
  by_cases hleaf : 2 ^ k ≤ m'
  · have hk : k - Nat.log 2 m - 1 = 0 := by
      have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hleaf
      omega
    rw [hk, sameG, ite_eq_left hleaf, mul_one, sameH]
    simp only [metricNk]
    rw [ite_eq_right (by omega), ← Real.exp_add, neg_add, show i.1 + 2 - 2 ^ k = m' - 2 ^ k by omega]
  · have hk : k - Nat.log 2 m - 1 = k - Nat.log 2 m' := by omega
    rw [sameG, ite_eq_right hleaf, hk]
    simp only [metricNk]
    rw [ite_eq_left (by omega)]

/-- **The recursion of the value**, at a node that isn't a 'leaf'. -/
theorem sameVal_recursion {ε M : ℝ} {m : ℕ} (h₁ : 1 ≤ m) (h₂ : m < 2 ^ k) (h₃ : m < 2 ^ (k + 1)) :
    sameVal k ε M (outTree m : Edge k) =
      1 / 4 * (0 + 0) +
      1 / 4 * (Real.exp (-(metricNk k ε M).length (leftArc m h₁ h₂)) * sameVal k ε M (leftArc m h₁ h₂) +
          (1 - Real.exp (-(metricNk k ε M).length (leftArc m h₁ h₂))) * 0) +
        1 / 4 * (Real.exp (-(metricNk k ε M).length (rightArc m h₁ h₂)) * sameVal k ε M (rightArc m h₁ h₂) +
          (1 - Real.exp (-(metricNk k ε M).length (rightArc m h₁ h₂))) * 0) := by
  rw [sameVal_outTree h₁ h₃]
  have hL : sameVal k ε M (leftArc m h₁ h₂) = sameG k ε M (2 * m) := by
    simp only [leftArc, sameVal]
    congr 1
    omega
  have hR : sameVal k ε M (rightArc m h₁ h₂) = sameG k ε M (2 * m + 1) := by
    simp only [rightArc, sameVal]
    congr 1
    omega
  have hl := exp_length_mul_sameG (ε := ε) (M := M) h₁ h₂ (m' := 2 * m) (Or.inl rfl) ⟨2 * m - 2, by have := two_pow_succ_eq k; omega⟩ (by simp only; omega)
  have hr := exp_length_mul_sameG (ε := ε) (M := M) h₁ h₂ (m' := 2 * m + 1) (Or.inr rfl) ⟨2 * m - 1, by have := two_pow_succ_eq k; omega⟩ (by simp only; omega)
  rw [hL, hR]
  simp only [leftArc, rightArc]
  rw [hl, hr, sameG, ite_eq_right (by omega)]
  have hlt : Nat.log 2 m < k := Nat.log_lt_of_lt_pow (by omega) h₂
  obtain ⟨j, hj⟩ : ∃ j, k - Nat.log 2 m = j + 1 := ⟨k - Nat.log 2 m - 1, by omega⟩
  rw [hj, sameH, Nat.add_sub_cancel]
  ring

/-! ### The potential -/

/-- The potential up to the 'leaves' of the inverted subtree: the probability, given the forests of a stage, that the lineages of `a` and `b` arrive at one 'leaf', not coalesced. -/
def PhiS (a b : X) (k : ℕ) (ε M : ℝ) (n : ℕ) (top : Edge k → Finset (Finset X)) : ℝ :=
  ∑ f, if SameAt a b n top f then sameVal k ε M f else 0

omit [Fintype X] in
theorem phiS_of_same {a b : X} {ε M : ℝ} {n : ℕ} {top : Edge k → Finset (Finset X)} {g : Edge k}
    (hg : SameAt a b n top g) (hs : ∀ f, SameAt a b n top f → f = g) : PhiS a b k ε M n top = sameVal k ε M g := by
  unfold PhiS
  rw [sum_eq_single g]
  · rw [ite_eq_left hg]
  · exact fun f _ hf => ite_eq_right fun hS => hf (hs f hS)
  · exact fun h' => absurd (mem_univ _) h'

omit [Fintype X] in
theorem phiS_of_none {a b : X} {ε M : ℝ} {n : ℕ} {top : Edge k → Finset (Finset X)}
    (hs : ∀ f, ¬ SameAt a b n top f) : PhiS a b k ε M n top = 0 := by
  unfold PhiS
  exact sum_eq_zero fun f _ => ite_eq_right (hs f)

section StepInner

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM in
/-- **The step of the chain at a node of the inverted subtree that isn't a 'leaf'.** -/
theorem phiS_step {n : ℕ} (hn : n + 1 < 2 ^ k) (h₃ : n + 1 < 2 ^ (k + 1)) (bot top : Edge k → Finset (Finset X))
    (hw : ∏ u ∈ stg k n, vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    PhiS a b k ε M n top *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto (networkNk k a b c d) (heapNode (n + 1) (by omega) h₃))ᶜ) ^ 2 =
      vertexKernel (networkNk k a b c d) (metricNk k ε M) 0 (heapNode (n + 1) (by omega) h₃)
        (arriving (networkNk k a b c d) (injNk k a b c d) top (heapNode (n + 1) (by omega) h₃)) fun t =>
          PhiS a b k ε M (n + 1) (overwrite (arcsInto (networkNk k a b c d) (heapNode (n + 1) (by omega) h₃)) top t) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hD := downClosed_stg (k := k) (a := a) (b := b) (c := c) (d := d) n
  set v : Vertex k X := heapNode (n + 1) (by omega) h₃ with hv
  have hvD : v ∉ stg k n := heapNode_notMem_stg h₃
  have hvr : v ≠ (networkNk k a b c d).root := (root_ne_heapNode).symm
  have hch := target_mem_stg_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃
  have hF := frontier_of_prod_ne_zero hN hinj hD hw
  have hout : ∀ g, (networkNk k a b c d).graph.source g = v ↔ g = outTree (n + 1) :=
    source_eq_inner_iff (by omega) hn h₃
  have hfrout : Fr n (outTree (n + 1) : Edge k) := fr_of_source_eq h₃ ((hout _).2 rfl)
  have harr : arriving (networkNk k a b c d) (injNk k a b c d) top v = top (outTree (n + 1)) :=
    arriving_inner (by omega) hn h₃ top
  have hL : (networkNk k a b c d).graph.target (leftArc (n + 1) (by omega) hn) = v :=
    (target_eq_inner_iff (by omega) hn _).2 (Or.inl rfl)
  have hR : (networkNk k a b c d).graph.target (rightArc (n + 1) (by omega) hn) = v :=
    (target_eq_inner_iff (by omega) hn _).2 (Or.inr rfl)
  by_cases hS : ∃ f, SameAt a b n top f
  · obtain ⟨f, hSf⟩ := hS
    have hsameuniq : ∀ g, SameAt a b n top g → g = f := fun g hg => eq_of_fr hF hg.1 hSf.1 hg.2.1 hSf.2.1
    rw [phiS_of_same hSf hsameuniq]
    by_cases hfv : (networkNk k a b c d).graph.source f = v
    · -- the lineages are together at `v`
      have hfout := (hout f).1 hfv
      subst hfout
      have hlow : lineages (top (outTree (n + 1))) = {a, b} := by
        ext x
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hx
          exact IsLow.of_reaches (reaches_of_mem hF hSf.1.1 hx) (isLow_target_outTree h₃)
        · rintro (rfl | rfl)
          · exact hSf.2.1
          · exact hSf.2.2.1
      have hpair := KernelBounds.eq_pair_of_lineages (hF.good_top _ (by
        rw [mem_stg, rk_target]
        exact hSf.1.1)) hab hlow hSf.2.2.2
      -- the other arcs that leave the next stage have neither lineage
      have hother : ∀ {g : Edge k}, Fr (n + 1) g → (networkNk k a b c d).graph.target g ≠ v → a ∉ lineages (top g) := by
        intro g hg htg hag
        have hgn : Fr n g := by
          refine ⟨?_, by have := hg.2; omega⟩
          have h1 := hg.1
          have h2 : tgtRk g ≠ n + 2 := fun h => htg (eq_heapNode_of_rk h₃ ((rk_target g).trans h))
          omega
        have hgf := eq_of_fr hF hgn hfrout hag hSf.2.1
        rw [hgf] at hg
        have := hg.2
        have h3 := fr_of_source_eq (a := a) (b := b) (c := c) (d := d) h₃ ((hout _).2 rfl)
        have h4 : srcRk (outTree (n + 1) : Edge k) = n + 2 := by
          rw [← rk_source (a := a) (b := b) (c := c) (d := d), (hout _).2 rfl, hv, rk_heapNode]
        omega
      have hsame_at : ∀ t : Edge k → Finset (Finset X), ∀ g,
          SameAt a b (n + 1) (overwrite (arcsInto (networkNk k a b c d) v) top t) g →
            g = leftArc (n + 1) (by omega) hn ∨ g = rightArc (n + 1) (by omega) hn := by
        intro t g hg
        by_cases htg : (networkNk k a b c d).graph.target g = v
        · exact (target_eq_inner_iff (by omega) hn g).1 htg
        · refine absurd ?_ (hother hg.1 htg)
          have := hg.2.1
          rwa [overwrite_of_notMem (fun h => htg (mem_arcsInto.1 h))] at this
      rw [harr, hpair, sameVal_recursion (ε := ε) (M := M) (by omega) hn h₃]
      symm
      refine KernelBounds.kernel_two_arcs_eq (leftArc_ne_rightArc _ (by omega) hn) hL hR
        (target_eq_inner_iff (by omega) hn · |>.1) rfl rfl hab ?_ ?_ ?_ ?_ ?_ ?_
      · -- different arcs, one way
        intro t h1 h2
        refine phiS_of_none fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h1] at this
          simp at this
          exact hab this.symm
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
          simp at this
          exact hab this
      · -- different arcs, the other way
        intro t h1 h2
        refine phiS_of_none fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h1] at this
          simp at this
          exact hab this
        · have := hg.2.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
          simp at this
          exact hab this.symm
      · -- the left arc, apart
        intro t h1 h2
        have h0 : overwrite (arcsInto (networkNk k a b c d) v) top t (leftArc (n + 1) (by omega) hn) = {{a}, {b}} := by
          rw [overwrite_of_mem (mem_arcsInto.2 hL)]
          exact h1
        refine phiS_of_same ⟨fr_leftIdx (by omega) hn, h0 ▸ left_mem_lineages_pair, h0 ▸ right_mem_lineages_pair,
          h0 ▸ pair_notMem_pair hab⟩ fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
          simp at this
      · -- the left arc, coalesced
        intro t h1 h2
        refine phiS_of_none fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.2.2
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h1] at this
          exact this (mem_insert_self _ _)
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h2] at this
          simp at this
      · -- the right arc, apart
        intro t h1 h2
        have h0 : overwrite (arcsInto (networkNk k a b c d) v) top t (rightArc (n + 1) (by omega) hn) = {{a}, {b}} := by
          rw [overwrite_of_mem (mem_arcsInto.2 hR)]
          exact h1
        refine phiS_of_same ⟨fr_rightIdx (by omega) hn, h0 ▸ left_mem_lineages_pair, h0 ▸ right_mem_lineages_pair,
          h0 ▸ pair_notMem_pair hab⟩ fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h2] at this
          simp at this
        · rfl
      · -- the right arc, coalesced
        intro t h1 h2
        refine phiS_of_none fun g hg => ?_
        rcases hsame_at t g hg with rfl | rfl
        · have := hg.2.1
          rw [overwrite_of_mem (mem_arcsInto.2 hL), h2] at this
          simp at this
        · have := hg.2.2.2
          rw [overwrite_of_mem (mem_arcsInto.2 hR), h1] at this
          exact this (mem_insert_self _ _)
    · -- the lineages are together on another arc
      refine vertexKernel_overwrite_eq hN hθ hρ hinj hD hvD hvr hch hw fun bot' top' htop' _ _ hF' => ?_
      rw [insert_heapNode_stg h₃] at hF'
      have htf := htop' f (target_ne_of_tgtRk_le h₃ hSf.1.1)
      have hSf' : SameAt a b (n + 1) top' f := ⟨fr_succ h₃ hSf.1 hfv, htf ▸ hSf.2.1, htf ▸ hSf.2.2.1, htf ▸ hSf.2.2.2⟩
      exact phiS_of_same hSf' fun g hg => eq_of_fr hF' hg.1 hSf'.1 hg.2.1 hSf'.2.1
  · -- the lineages have diverged, or coalesced
    rw [phiS_of_none fun f hf => hS ⟨f, hf⟩]
    refine vertexKernel_overwrite_eq hN hθ hρ hinj hD hvD hvr hch hw fun bot' top' htop' hmem hclust hF' => ?_
    rw [insert_heapNode_stg h₃] at hF'
    -- if both arrive at `v` they have coalesced, and stay so
    have hboth : ∀ {e₁ e₂ : Edge k}, (networkNk k a b c d).graph.target e₁ = v → (networkNk k a b c d).graph.target e₂ = v →
        a ∈ lineages (top' e₁) → b ∈ lineages (top' e₂) → ∃ e, (networkNk k a b c d).graph.target e = v ∧ ({a, b} : Finset X) ∈ top' e := by
      intro e₁ e₂ h1 h2 h3 h4
      have ha' := (hmem a).1 ⟨_, h1, h3⟩
      have hb' := (hmem b).1 ⟨_, h2, h4⟩
      rw [harr] at ha' hb'
      have hmem2 : ({a, b} : Finset X) ∈ top (outTree (n + 1)) := by
        by_contra hne
        exact hS ⟨_, hfrout, ha', hb', hne⟩
      exact hclust _ (by rw [harr]; exact hmem2)
    have hfrin : ∀ {e : Edge k}, (networkNk k a b c d).graph.target e = v → Fr (n + 1) e := by
      intro e he
      rcases (target_eq_inner_iff (by omega) hn e).1 he with rfl | rfl
      · exact fr_leftIdx (by omega) hn
      · exact fr_rightIdx (by omega) hn
    refine phiS_of_none fun g hg => ?_
    by_cases htg : (networkNk k a b c d).graph.target g = v
    · obtain ⟨e, he, hab'⟩ := hboth htg htg hg.2.1 hg.2.2.1
      have h3 := eq_of_fr hF' (hfrin he) hg.1 (mem_lineages.2 ⟨_, hab', by simp⟩) hg.2.1
      rw [h3] at hab'
      exact hg.2.2.2 hab'
    · refine hS ⟨g, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, by have := hg.1.2; omega⟩
        have h1 := hg.1.1
        have h2 : tgtRk g ≠ n + 2 := fun h => htg (eq_heapNode_of_rk h₃ ((rk_target g).trans h))
        omega
      · rw [← htop' g htg]
        exact hg.2.1
      · rw [← htop' g htg]
        exact hg.2.2.1
      · rw [← htop' g htg]
        exact hg.2.2.2

end StepInner

/-! ### The step at the cherry -/

section StepCherry

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ}

include hd hX in
/-- **The step of the chain at the cherry.** The lineages of `a` and `b` arrive at the stem, and stay apart along it with probability `exp (-ε)`. -/
theorem phiS_cherry (bot top : Edge k → Finset (Finset X))
    (hw : ∏ u ∈ stgT k, vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    (Real.exp (-ε) * sameVal k ε M .stem) *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto (networkNk k a b c d) .cherry)ᶜ) ^ 2 =
      vertexKernel (networkNk k a b c d) (metricNk k ε M) 0 .cherry
        (arriving (networkNk k a b c d) (injNk k a b c d) top .cherry) fun t =>
          PhiS a b k ε M 0 (overwrite (arcsInto (networkNk k a b c d) .cherry) top t) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hD := downClosed_stgT (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj hD hw
  have hbelow : ∀ {e : Edge k} {y x : X}, (networkNk k a b c d).graph.target e = .taxon y → x ∈ lineages (top e) → x = y := by
    intro e y x he hx
    obtain ⟨u, hu, hxu⟩ := hF.below e (by rw [he]; simp [rk]) x hx
    rw [he] at hu
    have h1 := eq_of_taxon_reaches hu
    have h2 := (mem_lineages_taxaInj.1 hxu).2
    rw [h1] at h2
    exact Vertex.taxon.inj h2
  have hin := eq_stem_of_target_eq_cherry (k := k) (a := a) (b := b) (c := c) (d := d)
  have hmem : (Edge.stem : Edge k) ∈ arcsInto (networkNk k a b c d) Vertex.cherry := mem_arcsInto.2 rfl
  rw [arriving_cherry hd hX hw]
  set S := arcsInto (networkNk k a b c d) Vertex.cherry with hS
  let g : Finset (Finset X) → ℝ := fun G => PhiS a b k ε M 0 (overwrite S top fun _ => G)
  have hψ : (fun t => PhiS a b k ε M 0 (overwrite S top t)) = fun t => g (t .stem) := by
    funext t
    change _ = PhiS a b k ε M 0 (overwrite S top fun _ => t .stem)
    congr 1
    funext f
    by_cases hf : f ∈ S
    · have : f = .stem := hin f (mem_arcsInto.1 hf)
      subst this
      rw [overwrite_of_mem hf, overwrite_of_mem hf]
    · rw [overwrite_of_notMem hf, overwrite_of_notMem hf]
  rw [hψ, vertexKernel_one_arc (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) (v := Vertex.cherry) (e := Edge.stem) le_rfl rfl hin rfl
    ⟨{a}, by simp⟩ g, sum_kingman_pair hab]
  -- only the stem has both lineages
  have hstem : ∀ (G : Finset (Finset X)) (f : Edge k), SameAt a b 0 (overwrite S top fun _ => G) f → f = .stem := by
    intro G f hf
    obtain ⟨⟨hf₁, hf₂⟩, ha, -, -⟩ := hf
    have h2 := two_pow_succ_eq k
    have h1 := one_le_two_pow_k k
    cases f with
    | rootTaxon =>
      rw [overwrite_of_notMem (by simp [hS])] at ha
      exact absurd (hbelow rfl ha) had
    | rootTop =>
      simp only [tgtRk] at hf₁
      omega
    | step t =>
      simp only [tgtRk] at hf₁
      omega
    | bottomTaxon =>
      rw [overwrite_of_notMem (by simp [hS])] at ha
      exact absurd (hbelow rfl ha) hac
    | tree m =>
      simp only [tgtRk] at hf₁
      omega
    | stem => rfl
    | cherryLeft =>
      simp only [srcRk] at hf₂
      omega
    | cherryRight =>
      simp only [srcRk] at hf₂
      omega
  have hg₁ : g {{a}, {b}} = sameVal k ε M .stem := by
    have h0 : overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem = {{a}, {b}} := overwrite_of_mem hmem _ _
    have ha' : a ∈ lineages (overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem) := by
      rw [h0]
      exact left_mem_lineages_pair
    have hb' : b ∈ lineages (overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem) := by
      rw [h0]
      exact right_mem_lineages_pair
    have hn' : ({a, b} : Finset X) ∉ overwrite S top (fun _ => ({{a}, {b}} : Finset (Finset X))) Edge.stem := by
      rw [h0]
      exact pair_notMem_pair hab
    exact phiS_of_same ⟨⟨by simp [tgtRk], by simp [srcRk]⟩, ha', hb', hn'⟩ (hstem _)
  have hg₂ : g (insert {a, b} {{a}, {b}}) = 0 := by
    refine phiS_of_none fun f hf => ?_
    have := hstem _ f hf
    subst this
    have h3 := hf.2.2.2
    rw [overwrite_of_mem hmem] at h3
    exact h3 (mem_insert_self _ _)
  rw [hg₁, hg₂, mul_zero, add_zero]
  rfl

end StepCherry

section Levels

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM in
/-- The mean of the potential doesn't change along the levels of the inverted subtree. -/
theorem stageMass_phiS {n : ℕ} (hn : n < 2 ^ k) :
    stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k n) (PhiS a b k ε M n) =
      (Real.exp (-ε) * sameVal k ε M .stem) * ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h2k := two_pow_succ_eq k
  induction n with
  | zero =>
    rw [← insert_cherry_stgT, ← stageMass_eq_insert downClosed_stgT (by simp [rk]) (fun e he => ?_) (phiS_cherry hd hX)]
    · exact stageMass_const hN hθ.isNormalized le_rfl hinj downClosed_stgT root_notMem_stgT _
    · have h1 := rk_target_lt_rk_source (a := a) (b := b) (c := c) (d := d) e
      rw [he] at h1
      have h2 : rk (Vertex.cherry : Vertex k X) = 1 := rfl
      rw [mem_stgT]
      omega
  | succ n ih =>
    have h₃ : n + 1 < 2 ^ (k + 1) := by omega
    rw [← insert_heapNode_stg h₃, ← stageMass_eq_insert (downClosed_stg n) (heapNode_notMem_stg h₃)
      (target_mem_stg_of_source_eq h₃) (phiS_step hd hX hε hM hn h₃)]
    exact ih (by omega)

end Levels

/-! ### The chain up the path, when one forest arrives on it -/

section Schedule

variable {R : Finset (Finset X) → ℝ} {A : Finset (Finset X)} {s₀ : ℕ}

/-- The arrivals on the path: the forest `A`, with `s₀` nodes left above. -/
def arrivalsAt (A : Finset (Finset X)) (s₀ s : ℕ) : Finset (Finset X) := if s = s₀ then A else ∅

theorem pvAt_above (M : ℝ) (s : ℕ) (hs : s ≤ s₀) (F : Finset (Finset X)) :
    pv (arrivalsAt A s₀) R M s F = ∑ H, kingmanTransition (pathTime M s) F H * R H := by
  induction s generalizing F with
  | zero =>
    simp only [pv, pathTime]
    rw [sum_kingman_zero]
  | succ s ih =>
    have harr : arrivalsAt A s₀ s = ∅ := ite_eq_right (by omega)
    simp only [pv, pathTime, harr, union_empty]
    simp only [ih (by omega)]
    rw [sum_kingman_comp]

theorem pvAt_at (M : ℝ) (F : Finset (Finset X)) :
    pv (arrivalsAt A s₀) R M (s₀ + 1) F = ∑ H, kingmanTransition (pathTime M (s₀ + 1)) (F ∪ A) H * R H := by
  have harr : arrivalsAt A s₀ s₀ = A := ite_eq_left rfl
  simp only [pv, pathTime, harr]
  simp only [pvAt_above M s₀ le_rfl]
  rw [sum_kingman_comp]

/-- **The chain up the path**, from the lineage of `c`: below the arrival it stays alone. -/
theorem pv_arrivalsAt (M : ℝ) (r : ℕ) (c : X) :
    pv (arrivalsAt A s₀) R M (s₀ + 1 + r) {{c}} = ∑ H, kingmanTransition (pathTime M (s₀ + 1)) ({{c}} ∪ A) H * R H := by
  induction r with
  | zero => exact pvAt_at M _
  | succ r ih =>
    have harr : arrivalsAt A s₀ (s₀ + 1 + r) = ∅ := ite_eq_right (by omega)
    rw [show s₀ + 1 + (r + 1) = (s₀ + 1 + r) + 1 by omega]
    simp only [pv, harr, union_empty]
    rw [sum_kingman_singleton, ih]

end Schedule

/-! ### The values at the top -/

section Values

variable (hd : ({a, b, c, d} : Finset X).card = 4)

omit [Fintype X] in
/-- The mass of a quartet tree with a cluster of `F` as a cherry is one. -/
theorem absVal_eq_one_of_mem [Fintype X] {r : QuartetTree X} {F : Finset (Finset X)} (hF : IsGoodForest F) {B : Finset X} (hB : B ∈ r.val) (hBF : B ∈ F) :
    absVal r F = 1 := by
  unfold absVal
  rw [← kingmanAbsorption_sum hF.1]
  refine sum_congr rfl fun H _ => ?_
  by_cases hA : kingmanAbsorption F H = 0
  · simp [hA]
  · exact ite_eq_left ⟨B, hB, (kingmanAbsorption_support_good hF hA).2.1 hBF⟩

omit [Fintype X] in
/-- The mass of a quartet tree whose cherries overlap a cluster of `F` is zero. -/
theorem absVal_eq_zero_of_overlap [Fintype X] {r : QuartetTree X} {F : Finset (Finset X)} (hF : IsGoodForest F) {C : Finset X} (hC : C ∈ F)
    (hr : ∀ B ∈ r.val, ¬ (B ⊆ C ∨ C ⊆ B ∨ Disjoint B C)) : absVal r F = 0 := by
  unfold absVal
  refine sum_eq_zero fun H _ => ?_
  by_cases hA : kingmanAbsorption F H = 0
  · simp [hA]
  · obtain ⟨hgood, hsub, -⟩ := kingmanAbsorption_support_good hF hA
    refine ite_eq_right ?_
    rintro ⟨B, hB, hBH⟩
    exact hr B hB (hgood.1.2 B hBH C (hsub hC))

omit [Fintype X] in
/-- A forest on an arc below the root stays good with the lineage of `d`. -/
theorem good_union_d [Fintype X] {S H : Finset (Finset X)} {T : ℝ} (hS : IsGoodForest S) (hdS : d ∉ lineages S) (hK : kingmanTransition T S H ≠ 0) :
    IsGoodForest (H ∪ {{d}}) := by
  obtain ⟨hgood, -, hlin⟩ := kingmanTransition_support_good hS hK
  refine IsGoodForest.union hgood ?_ ?_
  · have := isGoodForest_singletons ({d} : Finset X)
    simpa using this
  · rw [hlin]
    simpa [lineages] using hdS

omit [Fintype X] in
/-- **A cluster on the arc that is a cherry of the tree**: its mass is one. -/
theorem sum_kingman_absVal_of_mem [Fintype X] {S : Finset (Finset X)} (T : ℝ) (hS : IsGoodForest S) (hdS : d ∉ lineages S) {r : QuartetTree X} {B : Finset X}
    (hB : B ∈ r.val) (hBS : B ∈ S) : ∑ H, kingmanTransition T S H * absVal r (H ∪ {{d}}) = 1 := by
  rw [← kingmanTransition_sum hS.1 T]
  refine sum_congr rfl fun H _ => ?_
  by_cases hK : kingmanTransition T S H = 0
  · simp [hK]
  · rw [absVal_eq_one_of_mem (good_union_d hS hdS hK) hB
      (mem_union_left _ ((kingmanTransition_support_good hS hK).2.1 hBS)), mul_one]

omit [Fintype X] in
/-- **A cluster on the arc that overlaps the cherries of the tree**: its mass is zero. -/
theorem sum_kingman_absVal_of_overlap [Fintype X] {S : Finset (Finset X)} (T : ℝ) (hS : IsGoodForest S) (hdS : d ∉ lineages S) {r : QuartetTree X} {C : Finset X}
    (hC : C ∈ S) (hr : ∀ B ∈ r.val, ¬ (B ⊆ C ∨ C ⊆ B ∨ Disjoint B C)) : ∑ H, kingmanTransition T S H * absVal r (H ∪ {{d}}) = 0 := by
  refine sum_eq_zero fun H _ => ?_
  by_cases hK : kingmanTransition T S H = 0
  · simp [hK]
  · rw [absVal_eq_zero_of_overlap (good_union_d hS hdS hK) (mem_union_left _ ((kingmanTransition_support_good hS hK).2.1 hC)) hr, mul_zero]

omit [Fintype X] in
theorem pair_union_singleton {a b c : X} : ({{a}, {b}} ∪ {{c}} : Finset (Finset X)) = {{a}, {b}, {c}} := by
  ext A
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
theorem singleton_union_pair {a b c : X} : ({{c}} ∪ {{a}, {b}} : Finset (Finset X)) = {{a}, {b}, {c}} := by
  ext A
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
/-- The forest of two lineages coalesced is good. -/
theorem isGoodForest_coal [Fintype X] {a b : X} (hab : a ≠ b) : IsGoodForest (insert {a, b} {{a}, {b}} : Finset (Finset X)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro A hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl <;> simp
  · intro A hA B hB
    simp only [mem_insert, mem_singleton] at hA hB
    rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;> simp [hab, hab.symm]
  · intro A hA hA2
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact ⟨{a}, by simp, {b}, by simp, by simp [hab], rfl⟩
    · simp at hA2
    · simp at hA2

/-- Three lineages on an arc, and the lineage of `d` above it: the mass of a quartet tree. -/
def threeVal (a b c d : X) (T : ℝ) (r : QuartetTree X) : ℝ :=
  ∑ H, kingmanTransition T ({{a}, {b}, {c}} : Finset (Finset X)) H * absVal r (H ∪ {{d}})

omit [Fintype X] in
/-- The symmetry of the three lineages. -/
theorem threeVal_relabel [Fintype X] (π : Equiv.Perm X) (T : ℝ) (r : QuartetTree X)
    (h3 : relabelFamily π ({{a}, {b}, {c}} : Finset (Finset X)) = {{a}, {b}, {c}}) (h4 : relabelFamily π ({{d}} : Finset (Finset X)) = {{d}}) :
    threeVal a b c d T (relabelQuartet π r) = threeVal a b c d T r := by
  unfold threeVal
  rw [← (relabelFamilyEquiv π).sum_comp]
  refine sum_congr rfl fun H _ => ?_
  simp only [relabelFamilyEquiv_apply]
  have h1 : kingmanTransition T ({{a}, {b}, {c}} : Finset (Finset X)) (relabelFamily π H) = kingmanTransition T ({{a}, {b}, {c}} : Finset (Finset X)) H := by
    conv_lhs => rw [← h3]
    exact kingmanTransition_relabelFamily π T _ H
  have h2 : relabelFamily π H ∪ {{d}} = relabelFamily π (H ∪ {{d}}) := by
    unfold relabelFamily at h4 ⊢
    rw [image_union, h4]
  rw [h1, h2, absVal_relabel]

include hd

omit [Fintype X] in
theorem relabel_swap_bc : relabelQuartet (Equiv.swap b c) (quartetTree a b c d hd) = quartetTree a c b d (card_acbd hd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  apply Subtype.ext
  change relabelFamily (Equiv.swap b c) {{a, b}, {c, d}} = {{a, c}, {b, d}}
  have h1 : ({a, b} : Finset X).map (Equiv.swap b c).toEmbedding = {a, c} := by
    simp [Finset.map_insert, Equiv.swap_apply_of_ne_of_ne hab hac]
  have h2 : ({c, d} : Finset X).map (Equiv.swap b c).toEmbedding = {b, d} := by
    simp [Finset.map_insert, Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm]
  unfold relabelFamily
  rw [image_insert, image_singleton, h1, h2]

omit [Fintype X] in
theorem relabel_swap_ac : relabelQuartet (Equiv.swap a c) (quartetTree a b c d hd) = quartetTree a d b c (card_adbc hd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  apply Subtype.ext
  change relabelFamily (Equiv.swap a c) {{a, b}, {c, d}} = {{a, d}, {b, c}}
  have h1 : ({a, b} : Finset X).map (Equiv.swap a c).toEmbedding = {b, c} := by
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
    exact pair_comm _ _
  have h2 : ({c, d} : Finset X).map (Equiv.swap a c).toEmbedding = {a, d} := by
    rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne had.symm hcd.symm]
  unfold relabelFamily
  rw [image_insert, image_singleton, h1, h2, pair_comm]

variable (hX : Fintype.card X = 4)
include hX

/-- **Three lineages on an arc give each of the three trees with probability `1 / 3`**: by their symmetry, and since the entries sum to one on a species tree. -/
theorem threeVal_eq {T : ℝ} (hT : 0 < T) : threeVal a b c d T (quartetTree a b c d hd) = 1 / 3 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  set F3 : Finset (Finset X) := {{a}, {b}, {c}} with hF3
  have hset1 : relabelFamily (Equiv.swap b c) F3 = F3 := by
    rw [hF3]
    unfold relabelFamily
    ext A
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨B, rfl | rfl | rfl, rfl⟩
      · left
        simp [Equiv.swap_apply_of_ne_of_ne hab hac]
      · simp
      · simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨{a}, Or.inl rfl, by simp [Equiv.swap_apply_of_ne_of_ne hab hac]⟩
      · exact ⟨{c}, Or.inr (Or.inr rfl), by simp⟩
      · exact ⟨{b}, Or.inr (Or.inl rfl), by simp⟩
  have hset2 : relabelFamily (Equiv.swap a c) F3 = F3 := by
    rw [hF3]
    unfold relabelFamily
    ext A
    simp only [mem_image, mem_insert, mem_singleton]
    constructor
    · rintro ⟨B, rfl | rfl | rfl, rfl⟩
      · simp
      · right; left
        simp [Equiv.swap_apply_of_ne_of_ne hab.symm hbc]
      · simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨{c}, Or.inr (Or.inr rfl), by simp⟩
      · exact ⟨{b}, Or.inr (Or.inl rfl), by simp [Equiv.swap_apply_of_ne_of_ne hab.symm hbc]⟩
      · exact ⟨{a}, Or.inl rfl, by simp⟩
  have hd1 : relabelFamily (Equiv.swap b c) ({{d}} : Finset (Finset X)) = {{d}} := by
    simp [relabelFamily, Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm]
  have hd2 : relabelFamily (Equiv.swap a c) ({{d}} : Finset (Finset X)) = {{d}} := by
    simp [relabelFamily, Equiv.swap_apply_of_ne_of_ne had.symm hcd.symm]
  have e1 : threeVal a b c d T (quartetTree a c b d (card_acbd hd)) = threeVal a b c d T (quartetTree a b c d hd) := by
    rw [← relabel_swap_bc hd]
    exact threeVal_relabel _ T _ hset1 hd1
  have e2 : threeVal a b c d T (quartetTree a d b c (card_adbc hd)) = threeVal a b c d T (quartetTree a b c d hd) := by
    rw [← relabel_swap_ac hd]
    exact threeVal_relabel _ T _ hset2 hd2
  -- the entries sum to one on the species tree `((a, b), c), d)`
  have hN := isPhylogenetic_networkNk (k := 0) hd hX
  have hsum := sum_cfTriple_weak hN (isMetric_treeMetric hd hX one_pos hT).isNormalized hd
  have hS : IsGoodForest (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) := by
    refine IsGoodForest.union (isGoodForest_coal hab) ?_ ?_
    · simpa using isGoodForest_singletons ({c} : Finset X)
    · simp [lineages, hac.symm, hbc.symm]
  have hlin : d ∉ lineages (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) := by
    simp [lineages, had.symm, hbd.symm, hcd.symm]
  have hcf : ∀ r : QuartetTree X, nmscCF (networkNk 0 a b c d) (treeMetric 1 T) 0 r =
      Real.exp (-1) * threeVal a b c d T r + (1 - Real.exp (-1)) * ∑ H, kingmanTransition T (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) H * absVal r (H ∪ {{d}}) := by
    intro r
    rw [nmscCF_treeMetric hd hX one_pos hT r, sum_kingman_pair hab, threeVal, pair_union_singleton]
  have w1 : ∑ H, kingmanTransition T (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) H * absVal (quartetTree a b c d hd) (H ∪ {{d}}) = 1 :=
    sum_kingman_absVal_of_mem T hS hlin (B := {a, b}) (by simp [quartetTree]) (by simp)
  have w2 : ∑ H, kingmanTransition T (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) H * absVal (quartetTree a c b d (card_acbd hd)) (H ∪ {{d}}) = 0 := by
    refine sum_kingman_absVal_of_overlap T hS hlin (C := {a, b}) (by simp) fun B hB => ?_
    simp only [quartetTree, mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl <;> simp [subset_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm, had, had.symm, hbd, hbd.symm]
  have w3 : ∑ H, kingmanTransition T (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) H * absVal (quartetTree a d b c (card_adbc hd)) (H ∪ {{d}}) = 0 := by
    refine sum_kingman_absVal_of_overlap T hS hlin (C := {a, b}) (by simp) fun B hB => ?_
    simp only [quartetTree, mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl <;> simp [subset_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm, had, had.symm, hbd, hbd.symm]
  rw [hcf, hcf, hcf, w1, w2, w3, e1, e2] at hsum
  have hexp : Real.exp (-1) ≠ 0 := (Real.exp_pos _).ne'
  have : Real.exp (-1) * (3 * threeVal a b c d T (quartetTree a b c d hd) - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hexp
  · linarith

end Values

/-! ### The values on the path -/

section PathValues

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
include hd hX

/-- Lineages of `a`, `b`, `c` together on an arc, not coalesced. -/
theorem value_same {T : ℝ} (hT : 0 < T) :
    ∑ H, kingmanTransition T ({{c}} ∪ {{a}, {b}} : Finset (Finset X)) H * absVal (quartetTree a b c d hd) (H ∪ {{d}}) = 1 / 3 := by
  rw [← threeVal_eq hd hX hT, threeVal, singleton_union_pair]

omit hX in
/-- Lineages of `a`, `b` coalesced on the arc, with `c` on it: the gene tree has the cherry. -/
theorem value_coal (T : ℝ) :
    ∑ H, kingmanTransition T ({{c}} ∪ insert {a, b} {{a}, {b}} : Finset (Finset X)) H * absVal (quartetTree a b c d hd) (H ∪ {{d}}) = 1 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  refine sum_kingman_absVal_of_mem T ?_ ?_ (B := {a, b}) (by simp [quartetTree]) (by simp)
  · refine IsGoodForest.union ?_ (isGoodForest_coal hab) ?_
    · simpa using isGoodForest_singletons ({c} : Finset X)
    · simp [lineages, hac.symm, hbc.symm]
  · simp [lineages, had.symm, hbd.symm, hcd.symm]

/-- **On a species tree `(((c, x), y), d)`, the entry of `ab|cd`** is `exp (-L₁) / 3`. -/
theorem nmscCF_species_first {x y : X} (hxy : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) (hd' : ({c, x, y, d} : Finset X).card = 4) {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    nmscCF (networkNk 0 c x y d) (treeMetric L₁ L₂) 0 (quartetTree a b c d hd) = Real.exp (-L₁) / 3 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hcx : c ≠ x := by
    rcases hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hac.symm
    · exact hbc.symm
  have hcy : c ≠ y := by
    rcases hxy with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hbc.symm
    · exact hac.symm
  have hxy' : x ≠ y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  have hxd : x ≠ d := by
    rcases hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact had
    · exact hbd
  have hyd : y ≠ d := by
    rcases hxy with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hbd
    · exact had
  rw [nmscCF_treeMetric hd' hX h₁ h₂, sum_kingman_pair hcx]
  have h3 : ∑ H, kingmanTransition L₂ (({{c}, {x}} : Finset (Finset X)) ∪ {{y}}) H * absVal (quartetTree a b c d hd) (H ∪ {{d}}) = 1 / 3 := by
    rw [← value_same hd hX h₂]
    have hset : (({{c}, {x}} : Finset (Finset X)) ∪ {{y}}) = {{c}} ∪ {{a}, {b}} := by
      ext A
      simp only [mem_union, mem_insert, mem_singleton]
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    rw [hset]
  have h4 : ∑ H, kingmanTransition L₂ (insert {c, x} {{c}, {x}} ∪ {{y}} : Finset (Finset X)) H * absVal (quartetTree a b c d hd) (H ∪ {{d}}) = 0 := by
    refine sum_kingman_absVal_of_overlap L₂ ?_ ?_ (C := {c, x}) (by simp) fun B hB => ?_
    · refine IsGoodForest.union (isGoodForest_coal hcx) ?_ ?_
      · simpa using isGoodForest_singletons ({y} : Finset X)
      · simp [lineages, hcy.symm, hxy'.symm]
    · simp [lineages, hcd.symm, hxd.symm, hyd.symm]
    · simp only [quartetTree, mem_insert, mem_singleton] at hB
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hB with rfl | rfl <;>
        simp [subset_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm, had, had.symm, hbd, hbd.symm, hcd, hcd.symm]
  rw [h3, h4]
  ring

end PathValues

/-! ### The events at the 'leaves' -/

section Leaves

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ}

/-- The forest `A` is at the top of the arc to the 'leaf' `t`. -/
def AtLeaf (A : Finset (Finset X)) (t : ℕ) (top : Edge k → Finset (Finset X)) : Prop := top (outTree (2 ^ k + t)) = A

include hd hX in
/-- On the event that a forest of `a`, `b` is on the arc to the 'leaf' `t`, the other arcs to the 'leaves' have no lineage. -/
theorem top_outTree_eq_arrivalsAt {A : Finset (Finset X)} (hA : lineages A = {a, b}) {t : ℕ} (hk : 1 ≤ k) (ht : t < 2 ^ k)
    {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0)
    (hE : AtLeaf A t top) (n' : ℕ) (hn₁ : 2 ^ k ≤ n') (hn₃ : n' < 2 ^ (k + 1)) :
    top (outTree n') = arrivalsAt A (2 ^ k - 1 - t) (2 ^ (k + 1) - 1 - n') := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
  have h2k := two_pow_succ_eq k
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨t', rfl⟩ : ∃ t', n' = 2 ^ k + t' := ⟨n' - 2 ^ k, by omega⟩
  have ht' : t' < 2 ^ k := by omega
  have hindex : 2 ^ (k + 1) - 1 - (2 ^ k + t') = 2 ^ k - 1 - t' := by omega
  rw [hindex]
  unfold arrivalsAt
  by_cases htt : t' = t
  · subst htt
    rw [ite_eq_left rfl]
    exact hE
  · rw [ite_eq_right (by omega)]
    have hgood := (hF.good_top (outTree (2 ^ k + t')) (by
      rw [mem_stg, rk_target]
      have := tgtRk_pend (k := k) h2 ht'
      omega)).1
    refine eq_empty_of_lineages hgood (eq_empty_of_forall_notMem fun z hz => ?_)
    have hlow : z = a ∨ z = b := IsLow.of_reaches (reaches_of_mem hF (fr_pend h2 ht').1 hz) (isLow_target_outTree (by omega))
    have hz' : z ∈ lineages (top (outTree (2 ^ k + t))) := by
      unfold AtLeaf at hE
      rw [hE, hA]
      rcases hlow with rfl | rfl <;> simp
    exact htt (pend_inj h2 ht' ht (eq_of_fr hF (fr_pend h2 ht') (fr_pend h2 ht) hz hz'))

include hd hX in
/-- **The mass of a quartet tree on the event that a forest of `a`, `b` is on the arc to the 'leaf' `t`.** -/
theorem fullMass_atLeaf {A : Finset (Finset X)} (hA : lineages A = {a, b}) (hε : 0 < ε) (hM : 0 < M) {t : ℕ} (hk : 1 ≤ k) (ht : t < 2 ^ k) (r : QuartetTree X) :
    fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d)
        (fun top => (if AtLeaf A t top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root)) =
      (∑ H, kingmanTransition (pathTime M (2 ^ k - 1 - t + 1)) ({{c}} ∪ A) H * absVal r (H ∪ {{d}})) *
        fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if AtLeaf A t top then 1 else 0) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [fullMass_event hd hX hε hM r (B := arrivalsAt A (2 ^ k - 1 - t)) ?_ ?_]
  · congr 1
    have key := pv_arrivalsAt (A := A) (s₀ := 2 ^ k - 1 - t) (R := fun F => absVal r (F ∪ {{d}})) M t c
    rwa [show 2 ^ k - 1 - t + 1 + t = 2 ^ k by omega] at key
  · intro t₁ t₂ hh
    unfold AtLeaf
    rw [hh _ (tgtRk_pend h2 ht)]
  · intro bot top hw hE n' hn₁ hn₃
    exact top_outTree_eq_arrivalsAt hd hX hA hk ht hw hE n' hn₁ hn₃

include hd hX in
/-- **The partition.** The complement of the event of different edges is the disjoint union of the events on one arc to a 'leaf', coalesced or not. -/
theorem indicator_not_divAt (hk : 1 ≤ k) {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    (if ¬ DivAt a b (2 ^ k - 1) top then (1 : ℝ) else 0) =
      ∑ t ∈ range (2 ^ k), ((if AtLeaf {{a}, {b}} t top then 1 else 0) + (if AtLeaf (insert {a, b} {{a}, {b}}) t top then 1 else 0)) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
  have h2k := two_pow_succ_eq k
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- each of the two lineages is on an arc to a 'leaf'
  have hloc : ∀ {x : X}, x ≠ c → x ≠ d → ∃ t, t < 2 ^ k ∧ x ∈ lineages (top (outTree (2 ^ k + t))) := by
    intro x hxc hxd
    obtain ⟨m, hm, hx⟩ := exists_tree_of_stage hF (by omega) (by omega) hxc hxd
    obtain ⟨-, t, ht, hmt⟩ := exists_pend_of_fr hm
    exact ⟨t, ht, hmt ▸ hx⟩
  obtain ⟨ta, hta, haa⟩ := hloc hac had
  obtain ⟨tb, htb, hbb⟩ := hloc hbc hbd
  have huniq : ∀ {x : X} {t t' : ℕ}, t < 2 ^ k → t' < 2 ^ k → x ∈ lineages (top (outTree (2 ^ k + t))) →
      x ∈ lineages (top (outTree (2 ^ k + t'))) → t = t' := fun ht ht' hx hx' =>
    pend_inj h2 ht ht' (eq_of_fr hF (fr_pend h2 ht) (fr_pend h2 ht') hx hx')
  have hmem_of : ∀ {t : ℕ} {A : Finset (Finset X)}, lineages A = {a, b} → AtLeaf A t top → a ∈ lineages (top (outTree (2 ^ k + t))) ∧ b ∈ lineages (top (outTree (2 ^ k + t))) := by
    intro t A hA hE
    unfold AtLeaf at hE
    rw [hE, hA]
    simp
  have hlin1 : lineages ({{a}, {b}} : Finset (Finset X)) = {a, b} := by
    ext z
    simp
  have hlin2 : lineages (insert {a, b} {{a}, {b}} : Finset (Finset X)) = {a, b} := by
    ext z
    simp only [mem_lineages, mem_insert, mem_singleton]
    constructor
    · rintro ⟨A, rfl | rfl | rfl, hz⟩
      · simpa using hz
      · left
        simpa using hz
      · right
        simpa using hz
    · rintro (rfl | rfl)
      · exact ⟨_, Or.inr (Or.inl rfl), by simp⟩
      · exact ⟨_, Or.inr (Or.inr rfl), by simp⟩
  by_cases hdiv : DivAt a b (2 ^ k - 1) top
  · -- apart: no 'leaf' has both
    rw [ite_eq_right (not_not.2 hdiv)]
    symm
    refine sum_eq_zero fun t ht => ?_
    have htk := Finset.mem_range.1 ht
    obtain ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩ := hdiv
    have hnone : ∀ A : Finset (Finset X), lineages A = {a, b} → ¬ AtLeaf A t top := by
      intro A hA hE
      obtain ⟨ha', hb'⟩ := hmem_of hA hE
      have e1 := eq_of_fr hF hf₁ (fr_pend h2 htk) ha ha'
      have e2 := eq_of_fr hF hf₂ (fr_pend h2 htk) hb hb'
      exact hne (Edge.tree.inj (e1.trans e2.symm))
    rw [ite_eq_right (hnone _ hlin1), ite_eq_right (hnone _ hlin2), add_zero]
  · rw [ite_eq_left hdiv]
    -- together, at one 'leaf'
    have htab : ta = tb := by
      by_contra hne
      refine hdiv ?_
      have hf₁ := fr_pend (k := k) h2 hta
      have hf₂ := fr_pend (k := k) h2 htb
      have ha := haa
      have hb := hbb
      rw [outTree_pend h2 hta] at ha hf₁
      rw [outTree_pend h2 htb] at hb hf₂
      refine ⟨_, _, ?_, hf₁, hf₂, ha, hb⟩
      simp only [ne_eq, Fin.mk.injEq]
      omega
    subst htab
    have hlow : lineages (top (outTree (2 ^ k + ta))) = {a, b} := by
      ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hx
        exact IsLow.of_reaches (reaches_of_mem hF (fr_pend h2 hta).1 hx) (isLow_target_outTree (by omega))
      · rintro (rfl | rfl)
        · exact haa
        · exact hbb
    have hgood : IsGoodForest (top (outTree (2 ^ k + ta))) := hF.good_top _ (by
      rw [mem_stg, rk_target]
      have := tgtRk_pend (k := k) h2 hta
      omega)
    have hother : ∀ t ∈ range (2 ^ k), t ≠ ta → ((if AtLeaf {{a}, {b}} t top then (1 : ℝ) else 0) + (if AtLeaf (insert {a, b} {{a}, {b}}) t top then 1 else 0)) = 0 := by
      intro t ht hne
      have htk := Finset.mem_range.1 ht
      have hnone : ∀ A : Finset (Finset X), lineages A = {a, b} → ¬ AtLeaf A t top := fun A hA hE =>
        hne (huniq htk hta (hmem_of hA hE).1 haa)
      rw [ite_eq_right (hnone _ hlin1), ite_eq_right (hnone _ hlin2), add_zero]
    rw [sum_eq_single_of_mem ta (Finset.mem_range.2 hta) hother]
    by_cases hc : ({a, b} : Finset X) ∈ top (outTree (2 ^ k + ta))
    · -- coalesced
      have heq : top (outTree (2 ^ k + ta)) = insert {a, b} {{a}, {b}} := by
        ext B
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hB
          have hsub : B ⊆ {a, b} := hlow ▸ subset_lineages hB
          by_cases hcard : 2 ≤ #B
          · left
            exact Finset.eq_of_subset_of_card_le hsub (by rw [card_pair hab]; exact hcard)
          · have hne := hgood.1.1 B hB
            have h1 : #B = 1 := by
              have := Finset.card_pos.2 hne
              omega
            obtain ⟨z, rfl⟩ := Finset.card_eq_one.1 h1
            have hz := hsub (mem_singleton_self z)
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
        · have hpre : ∀ {z : X}, z ∈ ({a, b} : Finset X) → ({z} : Finset X) ∈ top (outTree (2 ^ k + ta)) := by
            intro z hz
            obtain ⟨B, hB, hzB⟩ := mem_lineages.1 (hlow ▸ hz : z ∈ lineages (top (outTree (2 ^ k + ta))))
            exact IsGoodForest.singleton_mem hgood hB hzB
          rintro (rfl | rfl | rfl)
          · exact hc
          · exact hpre (by simp)
          · exact hpre (by simp)
      have h1 : ¬ AtLeaf {{a}, {b}} ta top := by
        intro hE
        unfold AtLeaf at hE
        rw [hE] at hc
        exact pair_notMem_pair hab hc
      have h3 : AtLeaf (insert {a, b} {{a}, {b}}) ta top := heq
      rw [ite_eq_right h1, ite_eq_left h3, zero_add]
    · have heq := KernelBounds.eq_pair_of_lineages hgood hab hlow hc
      have h1 : AtLeaf {{a}, {b}} ta top := heq
      have h3 : ¬ AtLeaf (insert {a, b} {{a}, {b}}) ta top := by
        intro hE
        unfold AtLeaf at hE
        rw [hE] at heq
        exact hc (hE ▸ mem_insert_self _ _)
      rw [ite_eq_left h1, ite_eq_right h3, add_zero]

end Leaves

/-! ### The first entry -/

section First

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM

/-- A function of the arcs up to the 'leaves' has the same mean over the whole process as up to the stage of the 'leaves'. -/
theorem stageMass_eq_fullMass {φ : (Edge k → Finset (Finset X)) → ℝ} (hφ : ∀ t t' : Edge k → Finset (Finset X), (∀ f, tgtRk f ≤ 2 ^ k → t f = t' f) → φ t = φ t') :
    stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1)) φ =
      ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 * fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) φ := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  have hstg : (univ.erase (networkNk k a b c d).root) = stg k (2 ^ (k + 1) - 1) := stg_top.symm
  have htop := stageMass_top (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) hN (injNk k a b c d) φ
  rw [hstg] at htop
  rw [← htop]
  symm
  refine stageMass_marginal hN hθ.isNormalized le_rfl hinj (downClosed_stg _) (downClosed_stg _) (fun u hu => ?_) (root_notMem_stg (by omega)) _ fun t t' h => ?_
  · rw [mem_stg] at hu ⊢
    omega
  · refine hφ t t' fun f hf => h f ?_
    rw [mem_stg, rk_target]
    omega

/-- **The probability that the lineages of `a` and `b` arrive at one 'leaf' of the inverted subtree, not coalesced**: `p (p / 4) ^ k ∑_{t < 2 ^ k} exp (-t M)`. -/
theorem sum_fullMass_sameLeaf (hk : 1 ≤ k) :
    ∑ t ∈ range (2 ^ k), fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if AtLeaf {{a}, {b}} t top then 1 else 0) =
      Real.exp (-ε) * ((Real.exp (-ε) / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M))) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2k := two_pow_succ_eq k
  have hZ0 : ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
    positivity
  refine mul_left_cancel₀ hZ0 ?_
  have hm := stageMass_phiS (k := k) (a := a) (b := b) (c := c) (d := d) (n := 2 ^ k - 1) hd hX hε hM (by omega)
  have hval : sameVal k ε M Edge.stem = (Real.exp (-ε) / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)) := sameG_one hk ε M
  rw [hval] at hm
  rw [mul_comm _ (Real.exp (-ε) * _), ← hm, mul_sum]
  -- the potential at the stage of the 'leaves'
  have hend : stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1)) (PhiS a b k ε M (2 ^ k - 1)) =
      stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1))
        (fun top => ∑ t ∈ range (2 ^ k), if AtLeaf {{a}, {b}} t top then 1 else 0) := by
    refine stageMass_congr fun bot top hw => ?_
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
    by_cases hS : ∃ f, SameAt a b (2 ^ k - 1) top f
    · obtain ⟨f, hf⟩ := hS
      rw [phiS_of_same hf fun g hg => eq_of_fr hF hg.1 hf.1 hg.2.1 hf.2.1]
      -- the arc is one to a 'leaf'
      have hfa : ∃ t, t < 2 ^ k ∧ f = outTree (2 ^ k + t) := by
        obtain ⟨m, hm', hx⟩ := exists_tree_of_stage hF (by omega) (by omega) hac had
        obtain ⟨-, t, ht, hmt⟩ := exists_pend_of_fr hm'
        refine ⟨t, ht, ?_⟩
        rw [← hmt]
        exact eq_of_fr hF hf.1 hm' hf.2.1 hx
      obtain ⟨t, ht, rfl⟩ := hfa
      have hval' : sameVal k ε M (outTree (2 ^ k + t) : Edge k) = 1 := by
        rw [sameVal_outTree (by omega) (by omega), sameG, ite_eq_left (by omega)]
      have hlow : lineages (top (outTree (2 ^ k + t))) = {a, b} := by
        ext x
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hx
          exact IsLow.of_reaches (reaches_of_mem hF hf.1.1 hx) (isLow_target_outTree (by omega))
        · rintro (rfl | rfl)
          · exact hf.2.1
          · exact hf.2.2.1
      have hpair : AtLeaf {{a}, {b}} t top := KernelBounds.eq_pair_of_lineages (hF.good_top _ (by
        rw [mem_stg, rk_target]
        exact hf.1.1)) hab hlow hf.2.2.2
      rw [hval', sum_eq_single_of_mem t (Finset.mem_range.2 ht), ite_eq_left hpair]
      intro t' ht' hne
      refine ite_eq_right fun hE => hne ?_
      have ha' : a ∈ lineages (top (outTree (2 ^ k + t'))) := by
        unfold AtLeaf at hE
        rw [hE]
        simp
      exact pend_inj h2 (Finset.mem_range.1 ht') ht (eq_of_fr hF (fr_pend h2 (Finset.mem_range.1 ht')) hf.1 ha' hf.2.1)
    · rw [phiS_of_none fun f hf => hS ⟨f, hf⟩]
      symm
      refine sum_eq_zero fun t ht => ite_eq_right fun hE => hS ⟨outTree (2 ^ k + t), fr_pend h2 (Finset.mem_range.1 ht), ?_, ?_, ?_⟩
      · unfold AtLeaf at hE
        rw [hE]
        simp
      · unfold AtLeaf at hE
        rw [hE]
        simp
      · unfold AtLeaf at hE
        rw [hE]
        exact pair_notMem_pair hab
  rw [hend, stageMass_eq_fullMass hd hX hε hM (φ := fun top => ∑ t ∈ range (2 ^ k), if AtLeaf {{a}, {b}} t top then 1 else 0) ?_, fullMass_sum, mul_sum]
  intro t₁ t₂ hh
  refine sum_congr rfl fun t ht => ?_
  have : AtLeaf ({{a}, {b}} : Finset (Finset X)) t t₁ ↔ AtLeaf {{a}, {b}} t t₂ := by
    unfold AtLeaf
    rw [hh _ (tgtRk_pend h2 (Finset.mem_range.1 ht))]
  simp only [this]

/-- **The entry of `ab|cd` of `(1 - α) CF₂`.** On the complement of the event of different edges, the gene tree has the cherry `a, b` if they have coalesced, and if they arrive at a 'leaf' not coalesced then three lineages meet on the path, which gives `1 / 3`. -/
theorem eventMass_not_divAt (hk : 1 ≤ k) :
    eventMass k a b c d ε M (fun top => ¬ DivAt a b (2 ^ k - 1) top) (quartetTree a b c d hd) =
      1 - alpha k ε - 2 / 3 * (Real.exp (-ε) * ((Real.exp (-ε) / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)))) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hlin1 : lineages ({{a}, {b}} : Finset (Finset X)) = {a, b} := by
    ext z
    simp
  have hlin2 : lineages (insert {a, b} {{a}, {b}} : Finset (Finset X)) = {a, b} := by
    ext z
    simp only [mem_lineages, mem_insert, mem_singleton]
    constructor
    · rintro ⟨A, rfl | rfl | rfl, hz⟩
      · simpa using hz
      · left
        simpa using hz
      · right
        simpa using hz
    · rintro (rfl | rfl)
      · exact ⟨_, Or.inr (Or.inl rfl), by simp⟩
      · exact ⟨_, Or.inr (Or.inr rfl), by simp⟩
  set P : ℕ → ℝ := fun t => fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if AtLeaf {{a}, {b}} t top then 1 else 0) with hP
  set C : ℕ → ℝ := fun t => fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if AtLeaf (insert {a, b} {{a}, {b}}) t top then 1 else 0) with hC
  -- the total probability
  have htotal : ∑ t ∈ range (2 ^ k), (P t + C t) = 1 - alpha k ε := by
    have h1 := fullMass_one (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) hN hθ.isNormalized le_rfl
      (validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d))
    have h3 := fullMass_divAt (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM
    have h4 : fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if DivAt a b (2 ^ k - 1) top then 1 else 0) +
        fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if ¬ DivAt a b (2 ^ k - 1) top then 1 else 0) = 1 := by
      rw [← fullMass_add]
      refine Eq.trans (fullMass_congr (φ' := fun _ => 1) fun _ top _ => ?_) h1
      by_cases h : DivAt a b (2 ^ k - 1) top <;> simp [h]
    have h5 : fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if ¬ DivAt a b (2 ^ k - 1) top then 1 else 0) =
        ∑ t ∈ range (2 ^ k), (P t + C t) := by
      rw [fullMass_congr (φ' := fun top => ∑ t ∈ range (2 ^ k), ((if AtLeaf {{a}, {b}} t top then 1 else 0) + (if AtLeaf (insert {a, b} {{a}, {b}}) t top then 1 else 0))) fun _ top hw =>
        indicator_not_divAt hd hX hk (prod_stage_ne_zero hw), fullMass_sum]
      exact sum_congr rfl fun t _ => fullMass_add _ _ _
    linarith
  -- the masses
  have hmass : eventMass k a b c d ε M (fun top => ¬ DivAt a b (2 ^ k - 1) top) (quartetTree a b c d hd) = ∑ t ∈ range (2 ^ k), (1 / 3 * P t + C t) := by
    unfold eventMass
    rw [fullMass_congr (φ' := fun top => ∑ t ∈ range (2 ^ k),
      ((if AtLeaf {{a}, {b}} t top then 1 else 0) * absVal (quartetTree a b c d hd) (arriving (networkNk k a b c d) (injNk k a b c d) top .root) +
        (if AtLeaf (insert {a, b} {{a}, {b}}) t top then 1 else 0) * absVal (quartetTree a b c d hd) (arriving (networkNk k a b c d) (injNk k a b c d) top .root))) fun _ top hw => by
      have key : (if ¬ DivAt a b (2 ^ k - 1) top then (1 : ℝ) else 0) * absVal (quartetTree a b c d hd) (arriving (networkNk k a b c d) (injNk k a b c d) top .root) =
          ∑ t ∈ range (2 ^ k), ((if AtLeaf {{a}, {b}} t top then 1 else 0) * absVal (quartetTree a b c d hd) (arriving (networkNk k a b c d) (injNk k a b c d) top .root) +
            (if AtLeaf (insert {a, b} {{a}, {b}}) t top then 1 else 0) * absVal (quartetTree a b c d hd) (arriving (networkNk k a b c d) (injNk k a b c d) top .root)) := by
        rw [indicator_not_divAt hd hX hk (prod_stage_ne_zero hw), sum_mul]
        exact sum_congr rfl fun t _ => add_mul _ _ _
      convert key using 2
      congr, fullMass_sum]
    refine sum_congr rfl fun t ht => ?_
    have htk := Finset.mem_range.1 ht
    have hT : 0 < pathTime M (2 ^ k - 1 - t + 1) := pathTime_pos hM _
    rw [fullMass_add, fullMass_atLeaf hd hX hlin1 hε hM hk htk, fullMass_atLeaf hd hX hlin2 hε hM hk htk, value_same hd hX hT, value_coal hd, one_mul]
  have h6 : ∑ t ∈ range (2 ^ k), (1 / 3 * P t + C t) = 1 / 3 * ∑ t ∈ range (2 ^ k), P t + ∑ t ∈ range (2 ^ k), C t := by
    rw [sum_add_distrib, mul_sum]
  rw [sum_add_distrib] at htotal
  rw [hmass, h6, ← sum_fullMass_sameLeaf hd hX hε hM hk]
  linarith

/-- **The entry of `ab|cd` of `α CF₁`.** On the species trees with the 'leaves' `i < j`, the edge above the cherry has length `(j - i) M`, and the entry is `exp (-(j - i) M) / 3`. -/
theorem mul_cfOne_first :
    alpha k ε * cfOne k a b c d ε M (quartetTree a b c d hd) =
      2 / 3 * ∑ q ∈ leafPairs k, leafProb k a b c d ε M q * Real.exp (-(((q.2 - q.1 : ℕ) : ℝ) * M)) := by
  rw [mul_cfOne_eq_species hd hX hε hM, mul_sum]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨h1, h2, h3⟩ := mem_leafPairs hq
  have hL₁ : 0 < ((q.2 - q.1 : ℕ) : ℝ) * M := mul_pos (Nat.cast_pos.2 (by omega)) hM
  have hL₂ : 0 < pathTime M (2 ^ k - q.2) := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ k - q.2 = s + 1 := ⟨2 ^ k - q.2 - 1, by omega⟩
    rw [hs]
    exact pathTime_pos hM s
  have e1 := nmscCF_species_first hd hX (Or.inl ⟨rfl, rfl⟩) (card_species_ab hd) hL₁ hL₂
  have e2 := nmscCF_species_first hd hX (Or.inr ⟨rfl, rfl⟩) (card_species_ba hd) hL₁ hL₂
  unfold speciesMetric
  rw [e1, e2]
  ring

/-- **The first entry of `CF_abcd` on `𝒩(k)⁺`, exactly**, for `k ≥ 1`, `ε, M > 0`, with `p = exp (-ε)`: from `CF_abcd = α CF₁ + (1 - α) CF₂`. The last sum is over the pairs of 'leaves' `i < j`, and `leafProb` is the probability that the lineage of `a` reaches `i` and that of `b` reaches `j`, whose sum is `α / 2` (`alpha_eq_sum_leafProb`). -/
theorem cf_first_eq (hk : 1 ≤ k) :
    (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd).1 =
      1 - alpha k ε - 2 / 3 * (Real.exp (-ε) * ((Real.exp (-ε) / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)))) +
        2 / 3 * ∑ q ∈ leafPairs k, leafProb k a b c d ε M q * Real.exp (-(((q.2 - q.1 : ℕ) : ℝ) * M)) := by
  change nmscCF (networkNk k a b c d) (metricNk k ε M) 0 (quartetTree a b c d hd) = _
  rw [nmscCF_eq_mixture hd hX hε hM, mul_cfTwo hε, eventMass_not_divAt hd hX hε hM hk, mul_cfOne_first hd hX hε hM]
  ring

end First

/-! ### The limits at `M → 0⁺` and at `M → ∞` -/

section Limits

/-- **The first entry at `M → 0⁺`**: `1 - (2/3) α - (2/3) p (p/2)^k`. -/
def cfZero (k : ℕ) (ε : ℝ) : ℝ := 1 - 2 / 3 * alpha k ε - 2 / 3 * (Real.exp (-ε) * (Real.exp (-ε) / 2) ^ k)

/-- **The first entry at `M → ∞`**: `1 - α - (2/3) p (p/4)^k`. -/
def cfInfty (k : ℕ) (ε : ℝ) : ℝ := 1 - alpha k ε - 2 / 3 * (Real.exp (-ε) * (Real.exp (-ε) / 4) ^ k)

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM in
/-- The part of `α CF₁`: between `(α/3) exp (-(2^k - 1) M)` and `(α/3) exp (-M)`. -/
theorem sum_leafProb_bounds :
    alpha k ε / 3 * Real.exp (-(((2 ^ k - 1 : ℕ) : ℝ) * M)) ≤ 2 / 3 * ∑ q ∈ leafPairs k, leafProb k a b c d ε M q * Real.exp (-(((q.2 - q.1 : ℕ) : ℝ) * M)) ∧
      2 / 3 * ∑ q ∈ leafPairs k, leafProb k a b c d ε M q * Real.exp (-(((q.2 - q.1 : ℕ) : ℝ) * M)) ≤ alpha k ε / 3 * Real.exp (-M) := by
  have hα := alpha_eq_sum_leafProb (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM
  have hle : ∀ q ∈ leafPairs k, Real.exp (-(((2 ^ k - 1 : ℕ) : ℝ) * M)) ≤ Real.exp (-(((q.2 - q.1 : ℕ) : ℝ) * M)) ∧
      Real.exp (-(((q.2 - q.1 : ℕ) : ℝ) * M)) ≤ Real.exp (-M) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := mem_leafPairs hq
    constructor
    · refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ?_ hM.le))
      exact_mod_cast (by omega : q.2 - q.1 ≤ 2 ^ k - 1)
    · refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have : (1 : ℝ) ≤ ((q.2 - q.1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ q.2 - q.1)
      nlinarith
  have hsum : alpha k ε / 3 = 2 / 3 * ∑ q ∈ leafPairs k, leafProb k a b c d ε M q := by
    rw [hα]
    ring
  constructor
  · rw [hsum, mul_assoc, sum_mul]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun q hq => ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_left (hle q hq).1 (leafProb_nonneg hd hX hε hM q)
  · rw [hsum, mul_assoc, sum_mul]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun q hq => ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_left (hle q hq).2 (leafProb_nonneg hd hX hε hM q)

/-- The sum of the arrivals at one 'leaf' is continuous in `M`. -/
theorem continuous_sum_exp (k : ℕ) : Continuous fun M : ℝ => ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)) := by
  fun_prop

theorem tendsto_sum_exp_atTop : Tendsto (fun M : ℝ => ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M))) atTop (𝓝 1) := by
  have h2 : 0 < 2 ^ k := by positivity
  have hterm : ∀ t ∈ range (2 ^ k), Tendsto (fun M : ℝ => Real.exp (-((t : ℝ) * M))) atTop (𝓝 (if t = 0 then 1 else 0)) := by
    intro t _
    by_cases ht : t = 0
    · subst ht
      simp
    · rw [ite_eq_right ht]
      have ht' : (0 : ℝ) < t := Nat.cast_pos.2 (by omega)
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop ht'))
  have := tendsto_finsetSum (range (2 ^ k)) hterm
  simpa [Finset.sum_ite_eq', Finset.mem_range, h2] using this

include hd hX hε in
/-- **The limit of the first entry at `M → ∞`.** -/
theorem tendsto_cf_first_atTop (hk : 1 ≤ k) :
    Tendsto (fun M => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd).1) atTop (𝓝 (cfInfty k ε)) := by
  set p := Real.exp (-ε) with hp
  have hR : Tendsto (fun M : ℝ => 1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M))))) atTop (𝓝 (cfInfty k ε)) := by
    have := ((tendsto_sum_exp_atTop (k := k)).const_mul ((p / 4) ^ k)).const_mul p |>.const_mul (2 / 3 : ℝ) |>.const_sub (1 - alpha k ε)
    simpa [cfInfty, hp] using this
  have hU : Tendsto (fun M : ℝ => 1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)))) + alpha k ε / 3 * Real.exp (-M)) atTop (𝓝 (cfInfty k ε)) := by
    have := hR.add ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (alpha k ε / 3))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hR hU ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with M hM
    rw [cf_first_eq hd hX hε hM hk]
    have := (sum_leafProb_bounds (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM).1
    have h0 : 0 ≤ alpha k ε / 3 * Real.exp (-(((2 ^ k - 1 : ℕ) : ℝ) * M)) := mul_nonneg (div_nonneg (alpha_nonneg k ε) (by norm_num)) (Real.exp_pos _).le
    linarith
  · filter_upwards [eventually_gt_atTop 0] with M hM
    rw [cf_first_eq hd hX hε hM hk]
    have := (sum_leafProb_bounds (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM).2
    linarith

include hd hX hε in
/-- **The limit of the first entry at `M → 0⁺`.** -/
theorem tendsto_cf_first_zero (hk : 1 ≤ k) :
    Tendsto (fun M => (cfTriple (networkNk k a b c d) (metricNk k ε M) a b c d hd).1) (𝓝[>] 0) (𝓝 (cfZero k ε)) := by
  set p := Real.exp (-ε) with hp
  have hval0 : (∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * (0 : ℝ)))) = 2 ^ k := by
    simp
  have hexpz : ∀ c : ℝ, Tendsto (fun M : ℝ => Real.exp (-(c * M))) (𝓝[>] 0) (𝓝 1) := by
    intro c
    have hc : Continuous fun M : ℝ => Real.exp (-(c * M)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hR : Tendsto (fun M : ℝ => ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M))) (𝓝[>] 0) (𝓝 (2 ^ k)) := by
    have := ((continuous_sum_exp k).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [hval0] at this
  have hbase : Tendsto (fun M : ℝ => 1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M))))) (𝓝[>] 0)
      (𝓝 (1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * 2 ^ k)))) :=
    ((hR.const_mul ((p / 4) ^ k)).const_mul p |>.const_mul (2 / 3 : ℝ)).const_sub _
  have hgoal : 1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * 2 ^ k)) + alpha k ε / 3 = cfZero k ε := by
    have : (p / 4) ^ k * 2 ^ k = (p / 2) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    rw [this, cfZero, ← hp]
    ring
  have hL : Tendsto (fun M : ℝ => 1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)))) + alpha k ε / 3 * Real.exp (-(((2 ^ k - 1 : ℕ) : ℝ) * M))) (𝓝[>] 0) (𝓝 (cfZero k ε)) := by
    have := hbase.add ((hexpz ((2 ^ k - 1 : ℕ) : ℝ)).const_mul (alpha k ε / 3))
    rwa [mul_one, hgoal] at this
  have hU : Tendsto (fun M : ℝ => 1 - alpha k ε - 2 / 3 * (p * ((p / 4) ^ k * ∑ t ∈ range (2 ^ k), Real.exp (-((t : ℝ) * M)))) + alpha k ε / 3 * Real.exp (-M)) (𝓝[>] 0) (𝓝 (cfZero k ε)) := by
    have h1 : Tendsto (fun M : ℝ => Real.exp (-M)) (𝓝[>] 0) (𝓝 1) := by
      simpa using hexpz 1
    have := hbase.add (h1.const_mul (alpha k ε / 3))
    rwa [mul_one, hgoal] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with M hM
    rw [cf_first_eq hd hX hε hM hk]
    have := (sum_leafProb_bounds (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM).1
    linarith
  · filter_upwards [self_mem_nhdsWithin] with M hM
    rw [cf_first_eq hd hX hε hM hk]
    have := (sum_leafProb_bounds (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM).2
    linarith

end Limits

/-! ### The two limits differ -/

section Gap

variable {ε : ℝ}

omit [Fintype X] [DecidableEq X] in
theorem alpha_one (ε : ℝ) : alpha 1 ε = Real.exp (-ε) / 2 := by
  simp [alpha]

/-- **"By hand, at `k = 1`"**: the difference of the two limits is `p (1 - p) / 6`. -/
theorem cfZero_sub_cfInfty_one (ε : ℝ) : cfZero 1 ε - cfInfty 1 ε = Real.exp (-ε) * (1 - Real.exp (-ε)) / 6 := by
  simp only [cfZero, cfInfty, alpha_one, pow_one]
  ring

/-- With `x = p / 2`, a term of `α`. -/
theorem pow_le_alpha {k ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ k) (ε : ℝ) : (Real.exp (-ε) / 2) ^ ℓ ≤ alpha k ε :=
  single_le_sum (f := fun ℓ => (Real.exp (-ε) / 2) ^ ℓ) (fun _ _ => by positivity) (Finset.mem_Icc.2 ⟨h1, h2⟩)

/-- Two terms of `α`. -/
theorem pow_add_pow_le_alpha {k ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ + 1 ≤ k) (ε : ℝ) : (Real.exp (-ε) / 2) ^ ℓ + (Real.exp (-ε) / 2) ^ (ℓ + 1) ≤ alpha k ε := by
  have := sum_le_sum_of_subset_of_nonneg (f := fun ℓ => (Real.exp (-ε) / 2) ^ ℓ) (s := {ℓ, ℓ + 1}) (t := Finset.Icc 1 k)
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> exact Finset.mem_Icc.2 ⟨by omega, by omega⟩) (fun _ _ _ => by positivity)
  rwa [Finset.sum_pair (by omega)] at this

/-- **The two limits differ**, for every `k ≥ 1` and `ε > 0`. -/
theorem cfInfty_lt_cfZero (hk : 1 ≤ k) (hε : 0 < ε) : cfInfty k ε < cfZero k ε := by
  have hp0 : 0 < Real.exp (-ε) := Real.exp_pos _
  have hp1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
  · have := cfZero_sub_cfInfty_one ε
    have h2 : 0 < Real.exp (-ε) * (1 - Real.exp (-ε)) / 6 := by
      have : 0 < 1 - Real.exp (-ε) := by linarith
      positivity
    linarith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    set x := Real.exp (-ε) / 2 with hx
    have hp : Real.exp (-ε) = 2 * x := by rw [hx]; ring
    have hx0 : 0 < x := by rw [hx]; positivity
    have hx1 : x < 1 / 2 := by rw [hx]; linarith
    have hα : x ^ (j + 1) ≤ alpha (j + 2) ε := pow_le_alpha (by omega) (by omega) ε
    have hquarter : 0 < (Real.exp (-ε) / 4) ^ (j + 2) := by positivity
    have hpow : 0 < x ^ (j + 1) := by positivity
    unfold cfZero cfInfty
    rw [← hx]
    have hmain : Real.exp (-ε) * x ^ (j + 2) * 2 < x ^ (j + 1) := by
      rw [hp, pow_succ x (j + 1)]
      have : 4 * x * x < 1 := by nlinarith
      nlinarith
    have hq : 0 < Real.exp (-ε) * (Real.exp (-ε) / 4) ^ (j + 2) := by positivity
    linarith

end Gap

/-! ### On a species tree -/

section Tree

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4)
include hd hX

/-- **The first entry on the species tree `(((a, b), c), d)`**: `1 - (2/3) exp (-L₁)`, the formula of Allman et al. (2011). -/
theorem nmscCF_tree_first {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₂ : 0 < L₂) :
    nmscCF (networkNk 0 a b c d) (treeMetric L₁ L₂) 0 (quartetTree a b c d hd) = 1 - 2 / 3 * Real.exp (-L₁) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hw : ∑ H, kingmanTransition L₂ (insert {a, b} {{a}, {b}} ∪ {{c}} : Finset (Finset X)) H * absVal (quartetTree a b c d hd) (H ∪ {{d}}) = 1 := by
    refine sum_kingman_absVal_of_mem L₂ ?_ ?_ (B := {a, b}) (by simp [quartetTree]) (by simp)
    · refine IsGoodForest.union (isGoodForest_coal hab) ?_ ?_
      · simpa using isGoodForest_singletons ({c} : Finset X)
      · simp [lineages, hac.symm, hbc.symm]
    · simp [lineages, had.symm, hbd.symm, hcd.symm]
  have hv := threeVal_eq hd hX h₂
  rw [threeVal] at hv
  rw [nmscCF_treeMetric hd hX h₁ h₂, sum_kingman_pair hab, hw, pair_union_singleton, hv]
  ring

end Tree

end AllmanEtAl2023.NetworkNk
