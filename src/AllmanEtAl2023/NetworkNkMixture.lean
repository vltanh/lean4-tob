module

public import AllmanEtAl2023.NetworkNkSpecies

/-!
# Allman, Baños, Mitchell, Rhodes 2023: `CF_abcd = α CF₁ + (1 - α) CF₂`, in the proof of Proposition 1

"Now `CF_abcd` can be expressed as `CF_abcd = α CF₁ + (1 - α) CF₂`, where `CF₁` is the `CF` conditioned on the `a`, `b` lineages being on different edges at height `1 + (k + 1)ε` above the leaves, and `CF₂` the `CF` conditioned on the
complementary event."

* `cfOne`, `cfTwo`: these conditional masses; `nmscCF_eq_mixture`: the identity (`a:claim:prop1-mixture`).
* `ArrAt x y i j`: the lineages `x`, `y` have reached the 'leaves' `i`, `j` of the inverted subtree. The event of different edges is the disjoint union of these, for `i ≠ j` (`indicator_divAt`).
* `fullMass_arrAt`: on `ArrAt x y i j`, `i < j`, the masses are the concordance factors of the species tree `((c, x), y), d)` with edge `(j - i) M`, the paper's `(((c,a),b),d)` and `(((c,b),a),d)`.
* `fullMass_arrAt_swap`, `cfOne_second_eq_third`: the swap of `a` and `b`, an automorphism of `𝒩(k)⁺`. So the two trees have equal probability (`mul_cfOne_eq_species`, `alpha_eq_sum_leafProb`, `a:claim:prop1-cf1`).
* `cfOne_first_le`, `sum_cfOne`, `cfOne_second_bounds`: `CF₁` near `(0, 1/2, 1/2)` for large `M`. `cfTwo_nonneg`, `cfTwo_le_one`: the entries of `CF₂` are bounded.
* `nmscCF_first_le_of_mixture`: the first entry of `CF_abcd` is at most `(1 - α) + exp (-M)`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Phylogenetics.NMSC Finset AllmanEtAl2023.KernelBounds
open scoped Classical

namespace AllmanEtAl2023.NetworkNk

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} {a b c d : X}

/-! ### The arcs to the 'leaves' -/

/-- The lineages `x`, `y` have reached the 'leaves' `i`, `j` of the inverted subtree. -/
def ArrAt (x y : X) (i j : ℕ) (top : Edge k → Finset (Finset X)) : Prop :=
  x ∈ lineages (top (outTree (2 ^ k + i))) ∧ y ∈ lineages (top (outTree (2 ^ k + j)))

omit [Fintype X] [DecidableEq X] in
theorem outTree_pend {t : ℕ} (h2 : 2 ≤ 2 ^ k) (ht : t < 2 ^ k) :
    (outTree (2 ^ k + t) : Edge k) = .tree ⟨2 ^ k + t - 2, by have := two_pow_succ_eq k; omega⟩ :=
  outTree_of_two_le (by omega) (by have := two_pow_succ_eq k; omega)

omit [Fintype X] [DecidableEq X] in
theorem tgtRk_pend {t : ℕ} (h2 : 2 ≤ 2 ^ k) (ht : t < 2 ^ k) : tgtRk (outTree (2 ^ k + t) : Edge k) ≤ 2 ^ k := by
  rw [outTree_pend h2 ht]
  simp only [tgtRk]
  omega

omit [Fintype X] [DecidableEq X] in
theorem fr_pend {t : ℕ} (h2 : 2 ≤ 2 ^ k) (ht : t < 2 ^ k) : Fr (2 ^ k - 1) (outTree (2 ^ k + t) : Edge k) := by
  rw [outTree_pend h2 ht, fr_tree]
  simp only
  omega

omit [Fintype X] [DecidableEq X] in
theorem pend_inj {t t' : ℕ} (h2 : 2 ≤ 2 ^ k) (ht : t < 2 ^ k) (ht' : t' < 2 ^ k)
    (h : (outTree (2 ^ k + t) : Edge k) = outTree (2 ^ k + t')) : t = t' := by
  rw [outTree_pend h2 ht, outTree_pend h2 ht'] at h
  simp only [Edge.tree.injEq, Fin.mk.injEq] at h
  omega

omit [Fintype X] [DecidableEq X] in
/-- An arc of the subtree that leaves the stage of the 'leaves' is one of the arcs to them. -/
theorem exists_pend_of_fr {m : Fin (2 ^ (k + 1) - 2)} (h : Fr (2 ^ k - 1) (.tree m)) :
    2 ≤ 2 ^ k ∧ ∃ t, t < 2 ^ k ∧ (Edge.tree m : Edge k) = outTree (2 ^ k + t) := by
  have h1 := m.2
  have h2 := two_pow_succ_eq k
  have h3 := (fr_tree.1 h).2
  have h4 : 2 ≤ 2 ^ k := by omega
  refine ⟨h4, m.1 + 2 - 2 ^ k, by omega, ?_⟩
  rw [outTree_pend h4 (by omega)]
  congr 1
  apply Fin.ext
  simp only
  omega

/-- The parameters of the species tree of the 'leaves' `i < j`: "the length of the edge ancestral only to the cherry is `mM`", with `m = j - i`. -/
def speciesMetric (k : ℕ) (M : ℝ) (i j : ℕ) : MetricData (Edge 0) :=
  treeMetric (((j - i : ℕ) : ℝ) * M) (pathTime M (2 ^ k - j))

/-! ### The kernel above the stage, on two 'leaves' -/

section Arrivals

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} {x y : X} {i j : ℕ}

include hd hX in
/-- On the event that `x`, `y` have reached the 'leaves' `i`, `j`, the other arcs to the 'leaves' have no lineage: this is the schedule of the arrivals on the path. -/
theorem top_outTree_eq_arrivals (hxy : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) (hij : i < j) (hj : j < 2 ^ k)
    {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0)
    (hE : ArrAt x y i j top) (n' : ℕ) (hn₁ : 2 ^ k ≤ n') (hn₃ : n' < 2 ^ (k + 1)) :
    top (outTree n') = arrivals x y (2 ^ k - 1 - i) (2 ^ k - 1 - j) (2 ^ (k + 1) - 1 - n') := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
  have h2k := two_pow_succ_eq k
  have h2 : 2 ≤ 2 ^ k := by omega
  obtain ⟨t, rfl⟩ : ∃ t, n' = 2 ^ k + t := ⟨n' - 2 ^ k, by omega⟩
  have ht : t < 2 ^ k := by omega
  have hindex : 2 ^ (k + 1) - 1 - (2 ^ k + t) = 2 ^ k - 1 - t := by omega
  rw [hindex]
  have hgood := (hF.good_top (outTree (2 ^ k + t)) (by
    rw [mem_stg, rk_target]
    have := tgtRk_pend (k := k) h2 ht
    omega)).1
  -- a lineage on the arc is `x` at `i`, or `y` at `j`
  have hmem : ∀ z, z ∈ lineages (top (outTree (2 ^ k + t))) → (z = x ∧ t = i) ∨ (z = y ∧ t = j) := by
    intro z hz
    have hlow := IsLow.of_reaches (reaches_of_mem hF (fr_pend h2 ht).1 hz) (isLow_target_outTree (by omega))
    have hz' : z = x ∨ z = y := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hlow
      · exact hlow.symm
    rcases hz' with rfl | rfl
    · exact Or.inl ⟨rfl, pend_inj h2 ht (by omega) (eq_of_fr hF (fr_pend h2 ht) (fr_pend h2 (by omega)) hz hE.1)⟩
    · exact Or.inr ⟨rfl, pend_inj h2 ht hj (eq_of_fr hF (fr_pend h2 ht) (fr_pend h2 hj) hz hE.2)⟩
  unfold arrivals
  by_cases htj : t = j
  · subst htj
    rw [ite_eq_left rfl]
    refine eq_singleton_of_lineages hgood (ext fun z => ?_)
    simp only [mem_singleton]
    constructor
    · intro hz
      rcases hmem z hz with ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · exact h
    · rintro rfl
      exact hE.2
  by_cases hti : t = i
  · subst hti
    rw [ite_eq_right (by omega), ite_eq_left rfl]
    refine eq_singleton_of_lineages hgood (ext fun z => ?_)
    simp only [mem_singleton]
    constructor
    · intro hz
      rcases hmem z hz with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · omega
    · rintro rfl
      exact hE.1
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    refine eq_empty_of_lineages hgood (eq_empty_of_forall_notMem fun z hz => ?_)
    rcases hmem z hz with ⟨-, h⟩ | ⟨-, h⟩
    · exact hti h
    · exact htj h

include hd hX in
/-- **On the event that `x`, `y` have reached the 'leaves' `i < j`, "all coalescent events that can occur will have the same probability that they would if they instead occurred on a species tree"**: the mass of a quartet tree is the
probability of the event times its concordance factor on the species tree `(((c, x), y), d)`, in which "the length of the edge ancestral only to the cherry is `mM`", `m = j - i`. -/
theorem fullMass_arrAt (hε : 0 < ε) (hM : 0 < M) (hxy : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) (hij : i < j) (hj : j < 2 ^ k)
    (hd' : ({c, x, y, d} : Finset X).card = 4) (r : QuartetTree X) :
    fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d)
        (fun top => (if ArrAt x y i j top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root)) =
      nmscCF (networkNk 0 c x y d) (speciesMetric k M i j) 0 r *
        fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if ArrAt x y i j top then 1 else 0) := by
  have h2 : 2 ≤ 2 ^ k := by omega
  rw [fullMass_event hd hX hε hM r (B := arrivals x y (2 ^ k - 1 - i) (2 ^ k - 1 - j)) ?_ ?_]
  · congr 1
    rw [speciesMetric, nmscCF_treeMetric hd' hX ?_ ?_ r]
    · have key := pv_top (R := fun F => absVal r (F ∪ {{d}})) (x := x) (y := y) (sx := 2 ^ k - 1 - i) (sy := 2 ^ k - 1 - j) (by omega) M i c
      rw [show 2 ^ k - 1 - i + 1 + i = 2 ^ k by omega, show 2 ^ k - 1 - i - (2 ^ k - 1 - j) = j - i by omega,
        show 2 ^ k - 1 - j + 1 = 2 ^ k - j by omega] at key
      exact key
    · exact mul_pos (Nat.cast_pos.2 (by omega)) hM
    · obtain ⟨s, hs⟩ : ∃ s, 2 ^ k - j = s + 1 := ⟨2 ^ k - j - 1, by omega⟩
      rw [hs]
      exact pathTime_pos hM s
  · intro t t' hh
    unfold ArrAt
    rw [hh _ (tgtRk_pend h2 (by omega)), hh _ (tgtRk_pend h2 hj)]
  · intro bot top hw hE n' hn₁ hn₃
    exact top_outTree_eq_arrivals hd hX hxy hij hj hw hE n' hn₁ hn₃

end Arrivals

/-! ### The event is the union of the pairs of 'leaves' -/

omit [Fintype X] [DecidableEq X] in
/-- Lineages at two 'leaves' are on different arcs. -/
theorem divAt_of_arrAt [DecidableEq X] {i j : ℕ} {top : Edge k → Finset (Finset X)} (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hij : i ≠ j) (h : ArrAt a b i j top) :
    DivAt a b (2 ^ k - 1) top := by
  have h2 : 2 ≤ 2 ^ k := by omega
  have hf₁ := fr_pend (k := k) h2 hi
  have hf₂ := fr_pend (k := k) h2 hj
  obtain ⟨ha, hb⟩ := h
  rw [outTree_pend h2 hi] at ha hf₁
  rw [outTree_pend h2 hj] at hb hf₂
  refine ⟨_, _, ?_, hf₁, hf₂, ha, hb⟩
  simp only [ne_eq, Fin.mk.injEq]
  omega

/-- The pairs of 'leaves' `i < j`. -/
def leafPairs (k : ℕ) : Finset (ℕ × ℕ) := ((Finset.range (2 ^ k)) ×ˢ (Finset.range (2 ^ k))).filter fun p => p.1 < p.2

section Partition

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ}

include hd hX in
/-- The indicator of the event of different edges is the sum of those of the pairs of 'leaves', in the two orders. -/
theorem indicator_divAt {bot top : Edge k → Finset (Finset X)}
    (hw : ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0) :
    (if DivAt a b (2 ^ k - 1) top then (1 : ℝ) else 0) =
      ∑ p ∈ leafPairs k, ((if ArrAt a b p.1 p.2 top then 1 else 0) + (if ArrAt b a p.1 p.2 top then 1 else 0)) := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_stg _) hw
  have hmemP : ∀ {p : ℕ × ℕ}, p ∈ leafPairs k → p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ p.1 < p.2 := by
    intro p hp
    simp only [leafPairs, mem_filter, mem_product, Finset.mem_range] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  -- a lineage is at one 'leaf'
  have huniq : ∀ {x : X} {t t' : ℕ}, 2 ≤ 2 ^ k → t < 2 ^ k → t' < 2 ^ k → x ∈ lineages (top (outTree (2 ^ k + t))) →
      x ∈ lineages (top (outTree (2 ^ k + t'))) → t = t' := fun h2 ht ht' hx hx' =>
    pend_inj h2 ht ht' (eq_of_fr hF (fr_pend h2 ht) (fr_pend h2 ht') hx hx')
  by_cases hdiv : DivAt a b (2 ^ k - 1) top
  · rw [ite_eq_left hdiv]
    obtain ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩ := hdiv
    obtain ⟨h2, i, hi, hmi⟩ := exists_pend_of_fr hf₁
    obtain ⟨-, j, hj, hmj⟩ := exists_pend_of_fr hf₂
    rw [hmi] at ha
    rw [hmj] at hb
    have hij : i ≠ j := by
      rintro rfl
      exact hne (Edge.tree.inj (hmi.trans hmj.symm))
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hmem : (i, j) ∈ leafPairs k := by
        simp only [leafPairs, mem_filter, mem_product, Finset.mem_range]
        exact ⟨⟨hi, hj⟩, hlt⟩
      rw [sum_eq_single_of_mem (i, j) hmem]
      · have hA : ArrAt a b (i, j).1 (i, j).2 top := ⟨ha, hb⟩
        have hB : ¬ ArrAt b a (i, j).1 (i, j).2 top := fun h => hij (huniq h2 hi hj ha h.2)
        rw [ite_eq_left hA, ite_eq_right hB, add_zero]
      · intro p hp hpne
        obtain ⟨h1, h3, h4⟩ := hmemP hp
        rw [ite_eq_right, ite_eq_right, add_zero]
        · rintro ⟨h5, h6⟩
          have h7 := huniq h2 h1 hj h5 hb
          have h8 := huniq h2 h3 hi h6 ha
          omega
        · rintro ⟨h5, h6⟩
          have h7 := huniq h2 h1 hi h5 ha
          have h8 := huniq h2 h3 hj h6 hb
          exact hpne (Prod.ext h7 h8)
    · have hlt : j < i := by omega
      have hmem : (j, i) ∈ leafPairs k := by
        simp only [leafPairs, mem_filter, mem_product, Finset.mem_range]
        exact ⟨⟨hj, hi⟩, hlt⟩
      rw [sum_eq_single_of_mem (j, i) hmem]
      · have hA : ¬ ArrAt a b (j, i).1 (j, i).2 top := fun h => hij (huniq h2 hi hj ha h.1).symm.symm
        have hB : ArrAt b a (j, i).1 (j, i).2 top := ⟨hb, ha⟩
        rw [ite_eq_right hA, ite_eq_left hB, zero_add]
      · intro p hp hpne
        obtain ⟨h1, h3, h4⟩ := hmemP hp
        rw [ite_eq_right, ite_eq_right, add_zero]
        · rintro ⟨h5, h6⟩
          have h7 := huniq h2 h1 hj h5 hb
          have h8 := huniq h2 h3 hi h6 ha
          exact hpne (Prod.ext h7 h8)
        · rintro ⟨h5, h6⟩
          have h7 := huniq h2 h1 hi h5 ha
          have h8 := huniq h2 h3 hj h6 hb
          omega
  · rw [ite_eq_right hdiv]
    symm
    refine sum_eq_zero fun p hp => ?_
    obtain ⟨h1, h3, h4⟩ := hmemP hp
    have hA : ¬ ArrAt a b p.1 p.2 top := fun h => hdiv (divAt_of_arrAt h1 h3 (by omega) h)
    have hB : ¬ ArrAt b a p.1 p.2 top := fun h => hdiv (divAt_of_arrAt h3 h1 (by omega) ⟨h.2, h.1⟩)
    rw [ite_eq_right hA, ite_eq_right hB, add_zero]

include hd hX in
/-- **The probability of the event is `α`**, as a mean over the whole process. -/
theorem fullMass_divAt (hε : 0 < ε) (hM : 0 < M) :
    fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if DivAt a b (2 ^ k - 1) top then 1 else 0) = alpha k ε := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have hinj := validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d)
  have h1k := one_le_two_pow_k k
  have h2k := two_pow_succ_eq k
  have hstg : (univ.erase (networkNk k a b c d).root) = stg k (2 ^ (k + 1) - 1) := stg_top.symm
  have htop := stageMass_top (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) hN (injNk k a b c d)
    (fun top => if DivAt a b (2 ^ k - 1) top then 1 else 0)
  rw [hstg] at htop
  have hmarg : stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ (k + 1) - 1))
        (fun top => if DivAt a b (2 ^ k - 1) top then 1 else 0) =
      stageMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (stg k (2 ^ k - 1)) (fun top => if DivAt a b (2 ^ k - 1) top then 1 else 0) := by
    refine stageMass_marginal hN hθ.isNormalized le_rfl hinj (downClosed_stg _) (downClosed_stg _) (fun u hu => ?_) (root_notMem_stg (by omega)) _ fun t t' h => ?_
    · rw [mem_stg] at hu ⊢
      omega
    · have hc : DivAt a b (2 ^ k - 1) t ↔ DivAt a b (2 ^ k - 1) t' := by
        have hag : ∀ {m : Fin (2 ^ (k + 1) - 2)}, Fr (2 ^ k - 1) (.tree m) → t (.tree m) = t' (.tree m) := fun hf => h _ (by
          rw [mem_stg, rk_target]
          exact hf.1)
        constructor
        · rintro ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩
          exact ⟨m₁, m₂, hne, hf₁, hf₂, hag hf₁ ▸ ha, hag hf₂ ▸ hb⟩
        · rintro ⟨m₁, m₂, hne, hf₁, hf₂, ha, hb⟩
          exact ⟨m₁, m₂, hne, hf₁, hf₂, (hag hf₁).symm ▸ ha, (hag hf₂).symm ▸ hb⟩
      simp only [hc]
  have hZ0 : ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card (Edge k)) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
    positivity
  refine mul_left_cancel₀ hZ0 ?_
  rw [← htop, hmarg, stageMass_divAt hd hX hε hM]
  ring

end Partition

/-! ### The swap of `a` and `b` -/

section Swap

/-- The swap of the two arcs of the cherry. -/
def swapArc : Edge k → Edge k
  | .cherryLeft => .cherryRight
  | .cherryRight => .cherryLeft
  | e => e

omit [Fintype X] [DecidableEq X] in
theorem swapArc_involutive : Function.Involutive (swapArc : Edge k → Edge k) := by
  intro e
  cases e <;> rfl

/-- The swap of the two arcs of the cherry, as an equivalence. -/
def swapArcEquiv (k : ℕ) : Edge k ≃ Edge k := swapArc_involutive.toPerm

/-- The nodes under a permutation of the taxa. -/
def permVertex (π : Equiv.Perm X) : Vertex k X ≃ Vertex k X where
  toFun
    | .taxon x => .taxon (π x)
    | v => v
  invFun
    | .taxon x => .taxon (π.symm x)
    | v => v
  left_inv v := by cases v <;> simp
  right_inv v := by cases v <;> simp

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ}

/-- The histories under the swap of `a` and `b`. -/
abbrev swapTop (a b : X) (t : Edge k → Finset (Finset X)) : Edge k → Finset (Finset X) :=
  fun e => relabelFamily (Equiv.swap a b) (t ((swapArcEquiv k).symm e))

omit [Fintype X] in
theorem mem_lineages_swapTop {t : Edge k → Finset (Finset X)} {e : Edge k} {x : X} :
    x ∈ lineages (swapTop a b t e) ↔ Equiv.swap a b x ∈ lineages (t (swapArc e)) := by
  have he' : (swapArcEquiv k).symm e = swapArc e := rfl
  rw [swapTop, he', lineages_relabelFamily, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

omit [Fintype X] in
theorem swap_source (e : Edge k) :
    (networkNk k a b c d).graph.source (swapArcEquiv k e) = permVertex (Equiv.swap a b) ((networkNk k a b c d).graph.source e) := by
  cases e <;> rfl

omit [Fintype X] in
include hd in
theorem swap_target (e : Edge k) :
    (networkNk k a b c d).graph.target (swapArcEquiv k e) = permVertex (Equiv.swap a b) ((networkNk k a b c d).graph.target e) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  cases e with
  | rootTaxon =>
    change Vertex.taxon d = Vertex.taxon (Equiv.swap a b d)
    rw [Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  | bottomTaxon =>
    change Vertex.taxon c = Vertex.taxon (Equiv.swap a b c)
    rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  | cherryLeft =>
    change Vertex.taxon b = Vertex.taxon (Equiv.swap a b a)
    rw [Equiv.swap_apply_left]
  | cherryRight =>
    change Vertex.taxon a = Vertex.taxon (Equiv.swap a b b)
    rw [Equiv.swap_apply_right]
  | rootTop => rfl
  | step t => rfl
  | tree m => rfl
  | stem => rfl

/-- The lineages of all taxa under the swap. -/
theorem injNk_swap (v : Vertex k X) :
    injNk k a b c d (permVertex (Equiv.swap a b) v) = relabelFamily (Equiv.swap a b) (injNk k a b c d v) := by
  ext A
  simp only [injNk, taxaInj, relabelFamily, mem_image, mem_filter, mem_univ, true_and]
  cases v with
  | taxon y =>
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxy : x = Equiv.swap a b y := Vertex.taxon.inj hx
      subst hxy
      exact ⟨{y}, ⟨y, rfl, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hxy : x = y := Vertex.taxon.inj hx
      subst hxy
      exact ⟨Equiv.swap a b x, rfl, by simp⟩
  | root =>
    constructor
    · rintro ⟨x, hx, -⟩
      exact absurd (show Vertex.taxon x = Vertex.root from hx) (by simp)
    · rintro ⟨_, ⟨x, hx, -⟩, -⟩
      exact absurd (show Vertex.taxon x = Vertex.root from hx) (by simp)
  | cherry =>
    constructor
    · rintro ⟨x, hx, -⟩
      exact absurd (show Vertex.taxon x = Vertex.cherry from hx) (by simp)
    · rintro ⟨_, ⟨x, hx, -⟩, -⟩
      exact absurd (show Vertex.taxon x = Vertex.cherry from hx) (by simp)
  | heap n =>
    constructor
    · rintro ⟨x, hx, -⟩
      exact absurd (show Vertex.taxon x = Vertex.heap n from hx) (by simp)
    · rintro ⟨_, ⟨x, hx, -⟩, -⟩
      exact absurd (show Vertex.taxon x = Vertex.heap n from hx) (by simp)

include hd in
/-- **The mean under the swap of `a` and `b`**, an automorphism of `𝒩(k)⁺`. -/
theorem fullMass_swap (φ : (Edge k → Finset (Finset X)) → ℝ) :
    fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun t => φ (swapTop a b t)) =
      fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) φ :=
  fullMass_automorphism (fV := permVertex (Equiv.swap a b)) (fE := swapArcEquiv k) swap_source (swap_target hd) rfl
    (fun e => by cases e <;> rfl) (fun e => by cases e <;> rfl) injNk_swap φ

theorem arriving_root_swap (t : Edge k → Finset (Finset X)) :
    arriving (networkNk k a b c d) (injNk k a b c d) (swapTop a b t) .root =
      relabelFamily (Equiv.swap a b) (arriving (networkNk k a b c d) (injNk k a b c d) t .root) :=
  arriving_automorphism (fV := permVertex (Equiv.swap a b)) (fE := swapArcEquiv k) swap_source injNk_swap t .root

omit [Fintype X] in
theorem swapArc_outTree (m : ℕ) : swapArc (outTree m : Edge k) = outTree m := by
  simp only [outTree]
  split_ifs <;> rfl

omit [Fintype X] in
/-- Under the swap, the two lineages exchange their 'leaves'. -/
theorem arrAt_swapTop {i j : ℕ} {t : Edge k → Finset (Finset X)} : ArrAt a b i j (swapTop a b t) ↔ ArrAt b a i j t := by
  simp only [ArrAt, mem_lineages_swapTop, swapArc_outTree, Equiv.swap_apply_left, Equiv.swap_apply_right]

omit [Fintype X] in
theorem divAt_swapTop {n : ℕ} {t : Edge k → Finset (Finset X)} : DivAt a b n (swapTop a b t) ↔ DivAt a b n t := by
  have htree : ∀ m : Fin (2 ^ (k + 1) - 2), swapArc (Edge.tree m : Edge k) = .tree m := fun _ => rfl
  simp only [DivAt, mem_lineages_swapTop, htree, Equiv.swap_apply_left, Equiv.swap_apply_right]
  constructor
  · rintro ⟨m₁, m₂, hne, hf₁, hf₂, h1, h2⟩
    exact ⟨m₂, m₁, hne.symm, hf₂, hf₁, h2, h1⟩
  · rintro ⟨m₁, m₂, hne, hf₁, hf₂, h1, h2⟩
    exact ⟨m₂, m₁, hne.symm, hf₂, hf₁, h2, h1⟩

end Swap

/-! ### `α` -/

section Alpha

omit [Fintype X] [DecidableEq X] in
/-- The recursion of the geometric sum. -/
theorem sum_Icc_pow_succ (r : ℝ) (k : ℕ) : ∑ ℓ ∈ Finset.Icc 1 (k + 1), r ^ ℓ = r + r * ∑ ℓ ∈ Finset.Icc 1 k, r ^ ℓ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 := Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1) fun ℓ => r ^ ℓ
    rw [Finset.sum_Icc_succ_top (by omega)]
    linear_combination ih - r * h2

/-- `α` is the partial sum of a geometric series. -/
theorem alpha_eq_mul_sum_range (k : ℕ) (ε : ℝ) :
    alpha k ε = Real.exp (-ε) / 2 * ∑ i ∈ Finset.range k, (Real.exp (-ε) / 2) ^ i := by
  unfold alpha
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih, Finset.sum_Icc_succ_top (by omega)]
    ring

theorem alpha_nonneg (k : ℕ) (ε : ℝ) : 0 ≤ alpha k ε :=
  sum_nonneg fun _ _ => by positivity

theorem alpha_lt_one (k : ℕ) {ε : ℝ} (hε : 0 < ε) : alpha k ε < 1 := by
  have hp : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h0 := Real.exp_pos (-ε)
  unfold alpha
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_pow_succ]
    have h1 : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 k, (Real.exp (-ε) / 2) ^ ℓ := sum_nonneg fun _ _ => by positivity
    nlinarith

theorem alpha_pos {k : ℕ} (hk : 1 ≤ k) (ε : ℝ) : 0 < alpha k ε := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold alpha
  rw [sum_Icc_pow_succ]
  have h0 := Real.exp_pos (-ε)
  have h1 : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 k, (Real.exp (-ε) / 2) ^ ℓ := sum_nonneg fun _ _ => by positivity
  positivity

end Alpha

/-! ### The conditional concordance factors -/

section Conditional

variable (k) (a b c d) in
/-- The joint mass of the event `E` and of a gene tree with a cherry of `r`. -/
def eventMass (ε M : ℝ) (E : (Edge k → Finset (Finset X)) → Prop) (r : QuartetTree X) : ℝ :=
  fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d)
    (fun top => (if E top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root))

variable (k) (a b c d) in
/-- **`CF₁`**: "the `CF` conditioned on the `a`, `b` lineages being on different edges at height `1 + (k + 1)ε` above the leaves". -/
def cfOne (ε M : ℝ) (r : QuartetTree X) : ℝ := eventMass k a b c d ε M (DivAt a b (2 ^ k - 1)) r / alpha k ε

variable (k) (a b c d) in
/-- **`CF₂`**: "the `CF` conditioned on the complementary event". -/
def cfTwo (ε M : ℝ) (r : QuartetTree X) : ℝ := eventMass k a b c d ε M (fun top => ¬ DivAt a b (2 ^ k - 1) top) r / (1 - alpha k ε)

variable (hd : ({a, b, c, d} : Finset X).card = 4) (hX : Fintype.card X = 4) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)

include hd hX hε hM in
theorem eventMass_nonneg (E : (Edge k → Finset (Finset X)) → Prop) (r : QuartetTree X) : 0 ≤ eventMass k a b c d ε M E r := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  refine sum_nonneg fun bot _ => sum_nonneg fun top _ => ?_
  by_cases hw : injWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) bot top = 0
  · simp [hw]
  refine mul_nonneg (injWeight_nonneg_weak hθ ⟨le_rfl, zero_le_one⟩ _ _ _) (mul_nonneg ?_ ?_)
  · split_ifs
    · exact zero_le_one
    · exact le_rfl
  · exact absVal_nonneg r (good_arriving_root hN validInj_injNk hw).1.1

include hd hX hε hM in
/-- The joint mass is at most the probability of the event. -/
theorem eventMass_le (E : (Edge k → Finset (Finset X)) → Prop) (r : QuartetTree X) :
    eventMass k a b c d ε M E r ≤
      fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if E top then 1 else 0) := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  refine fullMass_mono hθ ⟨le_rfl, zero_le_one⟩ fun bot top hw => ?_
  have h1 := absVal_le_one r (good_arriving_root hN validInj_injNk hw).1.1
  have h0 := absVal_nonneg r (good_arriving_root hN validInj_injNk hw).1.1
  split_ifs
  · rw [one_mul]
    exact h1
  · rw [zero_mul]

include hd hX hε hM in
theorem mul_cfOne (r : QuartetTree X) : alpha k ε * cfOne k a b c d ε M r = eventMass k a b c d ε M (DivAt a b (2 ^ k - 1)) r := by
  unfold cfOne
  by_cases hα : alpha k ε = 0
  · have h1 := eventMass_le (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM (DivAt a b (2 ^ k - 1)) r
    rw [fullMass_divAt hd hX hε hM, hα] at h1
    have h2 := eventMass_nonneg (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM (DivAt a b (2 ^ k - 1)) r
    rw [hα, zero_mul]
    linarith
  · exact mul_div_cancel₀ _ hα

include hε in
theorem mul_cfTwo (r : QuartetTree X) :
    (1 - alpha k ε) * cfTwo k a b c d ε M r = eventMass k a b c d ε M (fun top => ¬ DivAt a b (2 ^ k - 1) top) r := by
  unfold cfTwo
  have h1 := alpha_lt_one k hε
  exact mul_div_cancel₀ _ (by linarith)

include hd hX hε hM in
/-- **`CF_abcd = α CF₁ + (1 - α) CF₂`** (`a:claim:prop1-mixture`), for each entry. -/
theorem nmscCF_eq_mixture (r : QuartetTree X) :
    nmscCF (networkNk k a b c d) (metricNk k ε M) 0 r =
      alpha k ε * cfOne k a b c d ε M r + (1 - alpha k ε) * cfTwo k a b c d ε M r := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have htaxa : r.taxa = univ := eq_univ_of_card _ (r.card_taxa.trans hX.symm)
  rw [nmscCF_eq_cherryMass_weak hN hθ.isNormalized le_rfl, htaxa, cherryMass_eq_fullMass, mul_cfOne hd hX hε hM, mul_cfTwo hε]
  unfold eventMass
  rw [← fullMass_add]
  refine fullMass_congr fun _ top _ => ?_
  by_cases h : DivAt a b (2 ^ k - 1) top
  · simp only [h, ↓reduceIte, not_true_eq_false, one_mul, zero_mul, add_zero]
    rfl
  · simp only [h, ↓reduceIte, not_false_eq_true, one_mul, zero_mul, zero_add]
    rfl

include hd hX hε hM in
theorem cfTwo_nonneg (r : QuartetTree X) : 0 ≤ cfTwo k a b c d ε M r :=
  div_nonneg (eventMass_nonneg hd hX hε hM _ r) (by linarith [alpha_lt_one k hε])

include hd hX hε hM in
/-- "We need not analyze `CF₂` (beyond knowing its entries are bounded)". -/
theorem cfTwo_le_one (r : QuartetTree X) : cfTwo k a b c d ε M r ≤ 1 := by
  have hN := isPhylogenetic_networkNk (k := k) hd hX
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  have h1 := alpha_lt_one k hε
  have h2 := eventMass_le (k := k) (a := a) (b := b) (c := c) (d := d) hd hX hε hM (fun top => ¬ DivAt a b (2 ^ k - 1) top) r
  have h4 := fullMass_one (N := networkNk k a b c d) (θ := metricNk k ε M) (ρ := 0) hN hθ.isNormalized le_rfl
    (validInj_injNk (k := k) (a := a) (b := b) (c := c) (d := d))
  have h3 : eventMass k a b c d ε M (fun top => ¬ DivAt a b (2 ^ k - 1) top) r ≤ 1 - alpha k ε := by
    refine h2.trans_eq ?_
    rw [eq_sub_iff_add_eq, ← fullMass_divAt (a := a) (b := b) (c := c) (d := d) hd hX hε hM, ← fullMass_add]
    refine Eq.trans (fullMass_congr (φ' := fun _ => 1) fun _ top _ => ?_) h4
    by_cases h : DivAt a b (2 ^ k - 1) top <;> simp [h]
  unfold cfTwo
  rw [div_le_one (by linarith)]
  exact h3

/-! ### `CF₁` from the species trees -/

/-- The species tree `(((c, a), b), d)`, or `(((c, x), y), d)`. -/
abbrev speciesTree (c x y d : X) : RootedNetwork (Vertex 0 X) (Edge 0) X := networkNk 0 c x y d

omit [Fintype X] in
include hd in
theorem card_species_ab : ({c, a, b, d} : Finset X).card = 4 := by
  rw [← hd]
  congr 1
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

omit [Fintype X] in
include hd in
theorem card_species_ba : ({c, b, a, d} : Finset X).card = 4 := by
  rw [← hd]
  congr 1
  ext z
  simp only [mem_insert, mem_singleton]
  tauto

include hd in
/-- "with each of these trees having equal probability": the swap of `a` and `b`. -/
theorem fullMass_arrAt_swap (i j : ℕ) :
    fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if ArrAt a b i j top then 1 else 0) =
      fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if ArrAt b a i j top then 1 else 0) := by
  rw [← fullMass_swap hd (ε := ε) (M := M) (fun top => if ArrAt b a i j top then (1 : ℝ) else 0)]
  refine fullMass_congr fun _ top _ => ?_
  have hswap : ArrAt b a i j (swapTop a b top) ↔ ArrAt a b i j top := by
    have h1 : swapTop a b top = swapTop b a top := by
      funext e
      simp only [swapTop, Equiv.swap_comm a b]
    rw [h1, arrAt_swapTop]
  simp only [hswap]

/-- The probability of the two lineages at the 'leaves' `p`. -/
abbrev leafProb (k : ℕ) (a b c d : X) (ε M : ℝ) (p : ℕ × ℕ) : ℝ :=
  fullMass (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) (fun top => if ArrAt a b p.1 p.2 top then 1 else 0)

theorem mem_leafPairs {p : ℕ × ℕ} (hp : p ∈ leafPairs k) : p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ p.1 < p.2 := by
  simp only [leafPairs, mem_filter, mem_product, Finset.mem_range] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem prod_stage_ne_zero {bot top : Edge k → Finset (Finset X)} (hw : injWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) bot top ≠ 0) :
    ∏ u ∈ stg k (2 ^ k - 1), vertexWeight (networkNk k a b c d) (metricNk k ε M) 0 (injNk k a b c d) u bot top ≠ 0 := by
  refine prod_ne_zero_iff.2 fun u hu => prod_ne_zero_iff.1 hw u ?_
  have hstg : (univ.erase (networkNk k a b c d).root) = stg k (2 ^ (k + 1) - 1) := stg_top.symm
  rw [hstg, mem_stg]
  rw [mem_stg] at hu
  have h2k := two_pow_succ_eq k
  have h1k := one_le_two_pow_k k
  omega

include hd hX hε hM in
/-- **`α = ∑ P`**: the event of different edges is the disjoint union of the pairs of 'leaves', in two orders of equal probability. -/
theorem alpha_eq_sum_leafProb : alpha k ε = 2 * ∑ p ∈ leafPairs k, leafProb k a b c d ε M p := by
  rw [← fullMass_divAt (a := a) (b := b) (c := c) (d := d) hd hX hε hM, fullMass_congr (φ' := fun top =>
    ∑ p ∈ leafPairs k, ((if ArrAt a b p.1 p.2 top then 1 else 0) + (if ArrAt b a p.1 p.2 top then 1 else 0))) fun _ top hw =>
    indicator_divAt hd hX (prod_stage_ne_zero hw), fullMass_sum, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [fullMass_add, ← fullMass_arrAt_swap hd p.1 p.2, two_mul]

include hd hX hε hM in
/-- **"To compute `CF₁`"** (`a:claim:prop1-cf1`). `α CF₁` is the mean over the pairs of 'leaves' `i < j` of the concordance factors on "a species tree with topology `(((c, a), b), d)` or a species tree with topology `(((c, b), a), d)`, with each of these
trees having equal probability", on which "the length of the edge ancestral only to the cherry is `mM`", `m = j - i`. Together with `alpha_eq_sum_leafProb`, `CF₁` is this mean. -/
theorem mul_cfOne_eq_species (r : QuartetTree X) :
    alpha k ε * cfOne k a b c d ε M r =
      ∑ p ∈ leafPairs k, leafProb k a b c d ε M p *
        (nmscCF (networkNk 0 c a b d) (speciesMetric k M p.1 p.2) 0 r + nmscCF (networkNk 0 c b a d) (speciesMetric k M p.1 p.2) 0 r) := by
  rw [mul_cfOne hd hX hε hM]
  unfold eventMass
  rw [fullMass_congr (φ' := fun top => ∑ p ∈ leafPairs k,
    ((if ArrAt a b p.1 p.2 top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root) +
      (if ArrAt b a p.1 p.2 top then 1 else 0) * absVal r (arriving (networkNk k a b c d) (injNk k a b c d) top .root))) fun _ top hw => by
    rw [indicator_divAt hd hX (prod_stage_ne_zero hw), sum_mul]
    exact sum_congr rfl fun p _ => add_mul _ _ _, fullMass_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := mem_leafPairs hp
  rw [fullMass_add, fullMass_arrAt hd hX hε hM (Or.inl ⟨rfl, rfl⟩) h3 h2 (card_species_ab hd) r,
    fullMass_arrAt hd hX hε hM (Or.inr ⟨rfl, rfl⟩) h3 h2 (card_species_ba hd) r, ← fullMass_arrAt_swap hd p.1 p.2]
  ring

omit [Fintype X] in
/-- The swap of `a`, `b` on the quartet trees. -/
theorem relabelQuartet_swap (hd : ({a, b, c, d} : Finset X).card = 4) :
    relabelQuartet (Equiv.swap a b) (quartetTree a c b d (card_acbd hd)) = quartetTree a d b c (card_adbc hd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  apply Subtype.ext
  change relabelFamily (Equiv.swap a b) {{a, c}, {b, d}} = {{a, d}, {b, c}}
  have h1 : ({a, c} : Finset X).map (Equiv.swap a b).toEmbedding = {b, c} := by
    ext z
    simp only [mem_map, mem_insert, mem_singleton, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨y, rfl | rfl, rfl⟩
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
        exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨a, Or.inl rfl, Equiv.swap_apply_left _ _⟩
      · exact ⟨z, Or.inr rfl, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm⟩
  have h2 : ({b, d} : Finset X).map (Equiv.swap a b).toEmbedding = {a, d} := by
    ext z
    simp only [mem_map, mem_insert, mem_singleton, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨y, rfl | rfl, rfl⟩
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
        exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨b, Or.inl rfl, Equiv.swap_apply_right _ _⟩
      · exact ⟨z, Or.inr rfl, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm⟩
  unfold relabelFamily
  rw [image_insert, image_singleton, h1, h2, pair_comm]

include hd in
/-- **"(q, p, p)" for `CF₁`**: the swap of `a`, `b` exchanges the two other entries of `CF₁`. -/
theorem cfOne_second_eq_third :
    cfOne k a b c d ε M (quartetTree a c b d (card_acbd hd)) = cfOne k a b c d ε M (quartetTree a d b c (card_adbc hd)) := by
  have key : eventMass k a b c d ε M (DivAt a b (2 ^ k - 1)) (quartetTree a c b d (card_acbd hd)) =
      eventMass k a b c d ε M (DivAt a b (2 ^ k - 1)) (quartetTree a d b c (card_adbc hd)) := by
    have hs := fullMass_swap (k := k) hd (ε := ε) (M := M) (fun top => (if DivAt a b (2 ^ k - 1) top then 1 else 0) *
      absVal (quartetTree a d b c (card_adbc hd)) (arriving (networkNk k a b c d) (injNk k a b c d) top .root))
    refine (fullMass_congr fun _ top _ => ?_).trans hs
    rw [arriving_root_swap, ← relabelQuartet_swap hd, absVal_relabel]
    simp only [divAt_swapTop]
  unfold cfOne
  rw [key]

/-! ### `CF₁` near `(0, 1/2, 1/2)` -/

include hX hM in
/-- On a species tree `(((c, x), y), d)`, a quartet tree other than `cx|yd` has a concordance factor at most `exp (-M)`, "by choosing `M` large enough, we can ensure with probability as close to 1 as we like that gene tree
topologies will match the population tree". -/
theorem nmscCF_species_le {x y : X} (hd' : ({c, x, y, d} : Finset X).card = 4) {i j : ℕ} (hij : i < j) (hj : j < 2 ^ k)
    {r : QuartetTree X} (hr : r ≠ quartetTree c x y d hd') :
    nmscCF (networkNk 0 c x y d) (speciesMetric k M i j) 0 r ≤ Real.exp (-M) := by
  have hN := isPhylogenetic_networkNk (k := 0) hd' hX
  have hL₁ : 0 < ((j - i : ℕ) : ℝ) * M := mul_pos (Nat.cast_pos.2 (by omega)) hM
  have hL₂ : 0 < pathTime M (2 ^ k - j) := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ k - j = s + 1 := ⟨2 ^ k - j - 1, by omega⟩
    rw [hs]
    exact pathTime_pos hM s
  have hθ := (isMetric_treeMetric hd' hX hL₁ hL₂).isWeakMetric
  have hs := splitOffAt_stem (k := 0) hd'
  have htaxa : r.taxa = (quartetTree c x y d hd').taxa :=
    (eq_univ_of_card _ (r.card_taxa.trans hX.symm)).trans (eq_univ_of_card _ ((quartetTree c x y d hd').card_taxa.trans hX.symm)).symm
  refine (nmscCF_le_exp_of_splitOffAt hN hθ ⟨le_rfl, zero_le_one⟩ (isDeletion_empty hN) (fun _ hf => absurd hf (Set.notMem_empty _)) hs htaxa hr).trans ?_
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  change M ≤ ((j - i : ℕ) : ℝ) * M
  have h1 : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - i)
  nlinarith

omit [Fintype X] in
include hd in
/-- `ab|cd` is not the split of the species tree `(((c, a), b), d)`. -/
theorem quartetTree_ne_species_ab [Fintype X] : quartetTree a b c d hd ≠ quartetTree c a b d (card_species_ab hd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  intro h
  have hv : ({{a, b}, {c, d}} : Finset (Finset X)) = {{c, a}, {b, d}} := congrArg Subtype.val h
  have hm : ({a, b} : Finset X) ∈ ({{c, a}, {b, d}} : Finset (Finset X)) := hv ▸ by simp
  simp only [mem_insert, mem_singleton, Finset.ext_iff] at hm
  rcases hm with hm | hm
  · rcases (hm b).1 (by simp) with h' | h'
    · exact hbc h'
    · exact hab h'.symm
  · rcases (hm a).1 (by simp) with h' | h'
    · exact hab h'
    · exact had h'

omit [Fintype X] in
include hd in
/-- `ab|cd` is not the split of the species tree `(((c, b), a), d)`. -/
theorem quartetTree_ne_species_ba [Fintype X] : quartetTree a b c d hd ≠ quartetTree c b a d (card_species_ba hd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four hd
  intro h
  have hv : ({{a, b}, {c, d}} : Finset (Finset X)) = {{c, b}, {a, d}} := congrArg Subtype.val h
  have hm : ({a, b} : Finset X) ∈ ({{c, b}, {a, d}} : Finset (Finset X)) := hv ▸ by simp
  simp only [mem_insert, mem_singleton, Finset.ext_iff] at hm
  rcases hm with hm | hm
  · rcases (hm a).1 (by simp) with h' | h'
    · exact hac h'
    · exact hab h'
  · rcases (hm b).1 (by simp) with h' | h'
    · exact hab h'.symm
    · exact hbd h'

include hd hX hε hM in
theorem leafProb_nonneg (p : ℕ × ℕ) : 0 ≤ leafProb k a b c d ε M p := by
  have hθ : (networkNk k a b c d).IsWeakMetric (metricNk k ε M) := (isMetric_metricNk hd hX hε hM).isWeakMetric
  refine sum_nonneg fun bot _ => sum_nonneg fun top _ => mul_nonneg (injWeight_nonneg_weak hθ ⟨le_rfl, zero_le_one⟩ _ _ _) ?_
  beta_reduce
  split_ifs
  · exact zero_le_one
  · exact le_rfl

include hd hX hε hM in
/-- **The first entry of `CF₁` is at most `exp (-M)`.** -/
theorem cfOne_first_le : cfOne k a b c d ε M (quartetTree a b c d hd) ≤ Real.exp (-M) := by
  by_cases hα : alpha k ε = 0
  · unfold cfOne
    rw [hα, div_zero]
    exact (Real.exp_pos _).le
  have hpos : 0 < alpha k ε := lt_of_le_of_ne (alpha_nonneg k ε) (Ne.symm hα)
  refine le_of_mul_le_mul_left ?_ hpos
  rw [mul_cfOne_eq_species hd hX hε hM, alpha_eq_sum_leafProb (a := a) (b := b) (c := c) (d := d) hd hX hε hM, mul_assoc, mul_comm 2, mul_assoc, sum_mul]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := mem_leafPairs hp
  refine mul_le_mul_of_nonneg_left ?_ (leafProb_nonneg hd hX hε hM p)
  have ha := nmscCF_species_le (k := k) hX hM (card_species_ab hd) h3 h2 (quartetTree_ne_species_ab hd)
  have hb := nmscCF_species_le (k := k) hX hM (card_species_ba hd) h3 h2 (quartetTree_ne_species_ba hd)
  linarith

include hd hX hε hM in
theorem cfOne_nonneg (r : QuartetTree X) : 0 ≤ cfOne k a b c d ε M r :=
  div_nonneg (eventMass_nonneg hd hX hε hM _ r) (alpha_nonneg k ε)

/-- The entries of `CF_abcd` sum to one, on any parameters whose sum at each node is one. -/
theorem sum_cfTriple_weak {V E : Type*} [Fintype V] [Fintype E] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsNormalized θ) {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    nmscCF N θ 0 (quartetTree a b c d h) + nmscCF N θ 0 (quartetTree a c b d (card_acbd h)) + nmscCF N θ 0 (quartetTree a d b c (card_adbc h)) = 1 := by
  have hs := sum_nmscCF_weak hN hθ (ρ := 0) le_rfl h
  have hc := card_treesOn h
  rw [treesOn_eq h] at hc hs
  have hne1 : quartetTree a b c d h ≠ quartetTree a c b d (card_acbd h) := by
    intro he
    rw [he] at hc
    have := Finset.card_le_two (a := quartetTree a c b d (card_acbd h)) (b := quartetTree a d b c (card_adbc h))
    rw [Finset.insert_idem] at hc
    omega
  have hne2 : quartetTree a b c d h ≠ quartetTree a d b c (card_adbc h) := by
    intro he
    have hs' : ({quartetTree a b c d h, quartetTree a c b d (card_acbd h), quartetTree a d b c (card_adbc h)} : Finset (QuartetTree X)) =
        {quartetTree a d b c (card_adbc h), quartetTree a c b d (card_acbd h)} := by
      rw [he]
      ext w
      simp only [mem_insert, mem_singleton]
      tauto
    rw [hs'] at hc
    have := Finset.card_le_two (a := quartetTree a d b c (card_adbc h)) (b := quartetTree a c b d (card_acbd h))
    omega
  have hne3 : quartetTree a c b d (card_acbd h) ≠ quartetTree a d b c (card_adbc h) := by
    intro he
    rw [he, Finset.pair_eq_singleton] at hc
    have := Finset.card_le_two (a := quartetTree a b c d h) (b := quartetTree a d b c (card_adbc h))
    omega
  rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_pair hne3, ← add_assoc] at hs
  exact hs

include hd hX hε hM in
/-- The entries of `CF₁` sum to one, for `k ≥ 1`. -/
theorem sum_cfOne (hk : 1 ≤ k) :
    cfOne k a b c d ε M (quartetTree a b c d hd) + cfOne k a b c d ε M (quartetTree a c b d (card_acbd hd)) +
      cfOne k a b c d ε M (quartetTree a d b c (card_adbc hd)) = 1 := by
  have hpos := alpha_pos (k := k) hk ε
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [mul_add, mul_add, mul_cfOne_eq_species hd hX hε hM, mul_cfOne_eq_species hd hX hε hM, mul_cfOne_eq_species hd hX hε hM, mul_one,
    ← sum_add_distrib, ← sum_add_distrib]
  conv_rhs => rw [alpha_eq_sum_leafProb (a := a) (b := b) (c := c) (d := d) hd hX hε hM, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := mem_leafPairs hp
  have hL₁ : 0 < ((p.2 - p.1 : ℕ) : ℝ) * M := mul_pos (Nat.cast_pos.2 (by omega)) hM
  have hL₂ : 0 < pathTime M (2 ^ k - p.2) := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ k - p.2 = s + 1 := ⟨2 ^ k - p.2 - 1, by omega⟩
    rw [hs]
    exact pathTime_pos hM s
  have hA := sum_cfTriple_weak (isPhylogenetic_networkNk (k := 0) (card_species_ab hd) hX)
    (isMetric_treeMetric (card_species_ab hd) hX hL₁ hL₂).isNormalized hd
  have hB := sum_cfTriple_weak (isPhylogenetic_networkNk (k := 0) (card_species_ba hd) hX)
    (isMetric_treeMetric (card_species_ba hd) hX hL₁ hL₂).isNormalized hd
  change _ = 2 * leafProb k a b c d ε M p
  unfold speciesMetric
  linear_combination (leafProb k a b c d ε M p) * hA + (leafProb k a b c d ε M p) * hB

include hd hX hε hM in
/-- **`CF₁` is near `(0, 1/2, 1/2)` for large `M`**: "making `CF₁` as close to `(0, 1/2, 1/2)` as desired". The other two entries are equal by the swap of `a`, `b`, and the first is at most `exp (-M)`. -/
theorem cfOne_second_bounds (hk : 1 ≤ k) :
    (1 - Real.exp (-M)) / 2 ≤ cfOne k a b c d ε M (quartetTree a c b d (card_acbd hd)) ∧
      cfOne k a b c d ε M (quartetTree a c b d (card_acbd hd)) ≤ 1 / 2 := by
  have h1 := sum_cfOne hd hX hε hM hk
  have h2 := cfOne_first_le hd hX hε hM (k := k)
  have h3 := cfOne_nonneg (k := k) hd hX hε hM (quartetTree a b c d hd)
  have h4 := cfOne_second_eq_third (k := k) hd (ε := ε) (M := M)
  rw [← h4] at h1
  constructor <;> linarith

include hd hX hε hM in
/-- **`CF_{ab|cd}` is at most `(1 - α) + exp (-M)`**, from `CF_abcd = α CF₁ + (1 - α) CF₂`, with the first entry of `CF₁` at most `exp (-M)` and that of `CF₂` at most 1. -/
theorem nmscCF_first_le_of_mixture :
    nmscCF (networkNk k a b c d) (metricNk k ε M) 0 (quartetTree a b c d hd) ≤ (1 - alpha k ε) + Real.exp (-M) := by
  rw [nmscCF_eq_mixture hd hX hε hM]
  have h1 := cfOne_first_le (k := k) hd hX hε hM
  have h2 := cfTwo_le_one (k := k) hd hX hε hM (quartetTree a b c d hd)
  have h3 := alpha_nonneg k ε
  have h4 := alpha_lt_one k hε
  have h5 := Real.exp_pos (-M)
  nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - alpha k ε)]

end Conditional

end AllmanEtAl2023.NetworkNk
