module

public import External.Rhodes2020.Theorem2
public import TINNiK.T3
public import TOBQMC.Level1CF

/-!
# NANUQ (Allman, Baños, Rhodes 2019)

E. Allman, H. Baños, J. Rhodes, *NANUQ: a method for inferring species networks from gene trees under the coalescent
model*, Algorithms Mol. Biol. 14 (2019), 24, <https://doi.org/10.1186/s13015-019-0159-2>, read in arXiv v1 (the line numbers below are those of its
plain text), and compared with the published text on the passages quoted.

## The algorithm

* Step 1, the counts: `quartetCount`, for gene trees on all the taxa. The source also allows trees on subsets, which
  is not modelled.
* Step 2, the tests and the classes of the sets of four taxa: `QuartetClass`, `classify`, with the star test
  `starPValue .lrt` and the T3 test `t3PValue`. The statistics are those printed (`starStat_eq_printed`,
  `t3Stat_eq_printed`). The source's selection of topologies: `IsMaxCountSelection`, `IsMinCountSelection`.
* Step 3, the network quartet distance: `rho`, `nanuqDistance`. It is not TINNiK's: the two differ at `x ≠ y` by the
  number of 4-cycles with `x, y` adjacent (`quartetDistance_sub_nanuqDistance`). On a classification without 4-cycles
  they agree (`nanuqDistance_eq_quartetDistance`), and on a tree it is the tree metric of Rhodes 2020
  (`nanuqDistance_treeClass`).
* Steps 4, 5 and the interpretation of the output are not formalized: NeighborNet, the Circular Network algorithm,
  splits graphs, Theorem 34, and with them the results on split systems (Theorem 15, Corollaries 16 and 24, Theorem
  23, Lemmas 19, 21, 25-28, 32, 33, Proposition 30). `theorem36_output` isolates what they would have to give.

## Theorem 36

* `theorem36_of_proposition9`: the source's consistency theorem, down to the distance of Step 3, which is what its
  proof shows; `theorem36_output_of_proposition9`, `theorem36_generic_of_proposition9`. `Proposition9.lean` proves
  Proposition 9 on binary level-1 networks, and there these are `theorem36`, `theorem36_output`, `theorem36_generic`.
* Their hypotheses: `ThreeTwoTreelike`, as printed; `Proposition9`, what is used of the source's Proposition 9; and
  `TINNiK.NoCentroidCF`, a correction.
* The population values: `cfClass`, the class given by the concordance factors; `networkClass`, the class given by the
  network, `networkDistance`, the theoretical distance of Definition 22, and `cfClass_eq_networkClass`.

## Two errors in the source's proof

1. "we choose `α_m` to be the minimum of the `α'_m`" (line 2207). It must be the maximum: `exists_levels`, and
   `not_rejects_at_minimum`. The theorem's statement is not affected.
2. "Since the network is binary, the true multinomial parameter values are `CF = (p₁, p₂, p₃)` with `p_i ≠ 1/3` or
   `0`" (line 2023). Tree-like, in Definition 8, includes the centroid, and by the source's formula a `3₂`-cycle
   reaches it (`figure5_centroid`), on the boundary of the tree-like region. There, at a fixed `β`, the star test
   rejects with probability only tending to `β`, and the distance does not agree with the theoretical one with
   probability tending to one (`not_tendsto_of_centroid`, `not_theorem36AsPrinted`). A concrete binary level-1 network
   and parameters where this happens, with the concordance factors derived from the definition of the NMSC, are in
   `ThreeTwoCycle.lean` (`ThreeTwo.not_theorem36AsPrinted_N₃`). The statement needs the extra hypothesis, which
   Proposition 10's condition gives (`figure5_lt`) and generic parameters give (`theorem36_generic_of_proposition9`).
   The source's proof also passes over the step that the maximum likelihood topologies are the true ones, with
   probability tending to one, which is `tendsto_maxCount_t3` and `tendsto_minCount`.

The strengthening of ECToBlob's Remark 8.3, with explicit levels, is in `src/ECToBlob/Remark83.lean`, from
`tendsto_classify_eq_cfClass`.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace External.AllmanBanosRhodes2019

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Steps 2 and 3 of the algorithm -/

/-- What Step 2 of the algorithm says of a set of four taxa: "(1) a star tree, (2) a resolved tree, or (3) a 4-cycle
network on the taxa" (line 1767). `tree s` is the quartet tree `s`. `cycle s` is the 4-cycle whose concordance factor
has its smallest entry at `s`: by Proposition 9(3), a 4-cycle in circular order `a, b, c, d` has `CF_AC|BD` smallest,
so `s = ac|bd`, and the two cherries of `s` are the two pairs of taxa opposite on the cycle. -/
inductive QuartetClass (X : Type*) [DecidableEq X] where
  | star : QuartetClass X
  | tree (s : QuartetTree X) : QuartetClass X
  | cycle (s : QuartetTree X) : QuartetClass X

/-- A selection of the maximum likelihood topology of a tree: "The MLE quartet tree topology is simply the quartet
topology with the largest count in the qcCF" (line 1905). -/
def IsMaxCountSelection (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) : Prop :=
  ∀ c q, q.card = 4 → ml c q ∈ treesOn q ∧ ∀ r ∈ treesOn q, c r ≤ c (ml c q)

/-- A selection of the maximum likelihood topology of a 4-cycle: it "is determined by which of the 3 triangular
regions in the simplex the normalized qcCF lies" (lines 1908-1910), which is the region of the topology of smallest
count (Figure 4 (R), Proposition 9(3)). -/
def IsMinCountSelection (ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X) : Prop :=
  ∀ c q, q.card = 4 → ml c q ∈ treesOn q ∧ ∀ r ∈ treesOn q, c (ml c q) ≤ c r

/-- **Step 2**, on the counts `c` of the quartet trees: the star test at level `β`, and the T3 test at level `α`, at
the topology of largest count. "With level `β` chosen for the test, we reject the star tree hypothesis for p-values
smaller than `β`" (line 1854); "we interpret a p-value greater than `α` as support for a tree [...]. A p-value less
than `α` is interpreted as support for a 4-cycle network" (lines 1901-1906); when the first fails to reject and the
second rejects, "We choose to prioritize the first test" (line 1916). A p-value equal to the level is not treated in
the source. Here it does not reject, as in `TINNiK.testedBT3`. -/
def classify (mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X) (α β : ℝ) (c : QuartetTree X → ℝ)
    (q : Finset X) : QuartetClass X :=
  if β ≤ starPValue .lrt c q then .star
  else if α ≤ t3PValue c (mlT c q) then .tree (mlT c q)
  else .cycle (mlC c q)

/-- `ρ_xy` of Definition 20 (lines 1026-1049), with the source's extension to a star tree (lines 1964-1968): `0` if
the quartet has the form `xy|zw`, `1/2` on a 4-cycle with `x, y` adjacent, and `1` otherwise. For `cycle s`, the taxa
`x, y` are adjacent when they are in different cherries of `s`. -/
def rho (C : QuartetClass X) (x y : X) : ℝ :=
  match C with
  | .star => 1
  | .tree s => if Separated s x y then 1 else 0
  | .cycle s => if Separated s x y then 1 / 2 else 1

/-- **Step 3, the network quartet distance** of Definition 22 (lines 1125-1132): for `x ≠ y`, `2 ∑_{z,w} ρ_xy(Q_xyzw)
+ 2n - 4`, the sum over the unordered pairs `z, w`, as in Theorem 17, that is, over the sets of four taxa containing
`x, y`. -/
def nanuqDistance (cl : Finset X → QuartetClass X) (x y : X) : ℝ :=
  if x = y then 0 else
    2 * ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q), rho (cl q) x y +
      2 * (Fintype.card X : ℝ) - 4

/-- The distance depends only on the classes of the sets of four taxa. -/
theorem nanuqDistance_congr {cl cl' : Finset X → QuartetClass X} (h : ∀ q : Finset X, q.card = 4 → cl q = cl' q) :
    nanuqDistance cl = nanuqDistance cl' := by
  funext x y
  unfold nanuqDistance
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, ↓reduceIte]
    congr 3
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [h q (Finset.mem_filter.mp hq).2.1]

/-! ### The concordance factor's class -/

/-- `s` has strictly the least concordance factor on its taxa. -/
def IsStrictMin (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop := ∀ r ∈ s.alternatives, p s < p r

/-- **The population value of Step 2**: the answer that the tests of Step 2 aim at for the concordance factors `p`:
the star tree at the centroid; the quartet tree `s` when `p` is strictly on the half-line of `s`, what Definition 8
calls "tree-like" and "supports"; and, off these, the topology of least concordance factor, a non-tree-like
concordance factor being judged a 4-cycle by NANUQ (lines 1874-1881). `cfClass_eq_tree`, `cfClass_eq_cycle` and
`cfClass_eq_star` are the cases. -/
def cfClass (p : QuartetTree X → ℝ) (q : Finset X) : QuartetClass X :=
  if h : ∃ s ∈ treesOn q, IsT1Strict p s then .tree h.choose
  else if h' : ∃ s ∈ treesOn q, IsStrictMin p s then .cycle h'.choose
  else .star

theorem IsT1Strict.unique {p : QuartetTree X → ℝ} {s s' : QuartetTree X} (h : IsT1Strict p s)
    (h' : IsT1Strict p s') (hq : s.taxa = s'.taxa) : s = s' := by
  by_contra hne
  exact lt_asymm (h.1 s' (QuartetTree.mem_alternatives.2 ⟨hq.symm, Ne.symm hne⟩))
    (h'.1 s (QuartetTree.mem_alternatives.2 ⟨hq, hne⟩))

theorem IsStrictMin.unique {p : QuartetTree X → ℝ} {s s' : QuartetTree X} (h : IsStrictMin p s)
    (h' : IsStrictMin p s') (hq : s.taxa = s'.taxa) : s = s' := by
  by_contra hne
  exact lt_asymm (h s' (QuartetTree.mem_alternatives.2 ⟨hq.symm, Ne.symm hne⟩))
    (h' s (QuartetTree.mem_alternatives.2 ⟨hq, hne⟩))

/-- The trees on the taxa of `s` other than `s` and one alternative. -/
private theorem other_alternative {s r r₁ r₂ : QuartetTree X} (h : s.alternatives = {r₁, r₂})
    (hr : r ∈ r₁.alternatives) : r = s ∨ r = r₂ := by
  obtain ⟨hrt, hrne⟩ := QuartetTree.mem_alternatives.1 hr
  have h₁ : r₁ ∈ s.alternatives := by rw [h]; simp
  have ht₁ := (QuartetTree.mem_alternatives.1 h₁).1
  by_cases hrs : r = s
  · exact Or.inl hrs
  · have hmem : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hrt.trans ht₁, hrs⟩
    rw [h] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact absurd h' hrne
    · exact Or.inr h'

/-- A strict minimum and a point strictly on a half-line exclude each other. -/
theorem not_isT1Strict_of_isStrictMin {p : QuartetTree X → ℝ} {s s' : QuartetTree X} (h : IsStrictMin p s)
    (h' : IsT1Strict p s') (hq : s.taxa = s'.taxa) : False := by
  by_cases hss : s = s'
  · subst hss
    obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
    have hr : r₁ ∈ s.alternatives := by rw [ha]; simp
    exact lt_asymm (h r₁ hr) (h'.1 r₁ hr)
  · obtain ⟨r₁, r₂, hne, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s'
    have hs : s ∈ s'.alternatives := QuartetTree.mem_alternatives.2 ⟨hq, hss⟩
    have hr₁ : r₁ ∈ s'.alternatives := by rw [ha]; simp
    have hr₂ : r₂ ∈ s'.alternatives := by rw [ha]; simp
    by_cases h₁ : s = r₁
    · have halt : r₂ ∈ s.alternatives := QuartetTree.mem_alternatives.2
        ⟨(QuartetTree.mem_alternatives.1 hr₂).1.trans hq.symm, fun he => hne (he.trans h₁).symm⟩
      exact (h r₂ halt).ne (h'.2 s hs r₂ hr₂)
    · have halt : r₁ ∈ s.alternatives := QuartetTree.mem_alternatives.2
        ⟨(QuartetTree.mem_alternatives.1 hr₁).1.trans hq.symm, fun he => h₁ he.symm⟩
      exact (h r₁ halt).ne (h'.2 s hs r₁ hr₁)

theorem cfClass_eq_tree {p : QuartetTree X → ℝ} {q : Finset X} {s : QuartetTree X} (hs : s ∈ treesOn q)
    (h : IsT1Strict p s) : cfClass p q = .tree s := by
  have hex : ∃ s ∈ treesOn q, IsT1Strict p s := ⟨s, hs, h⟩
  rw [cfClass, dite_eq_left hex]
  congr 1
  exact IsT1Strict.unique hex.choose_spec.2 h
    ((mem_treesOn.1 hex.choose_spec.1).trans (mem_treesOn.1 hs).symm)

theorem cfClass_eq_cycle {p : QuartetTree X → ℝ} {q : Finset X} {s : QuartetTree X} (hs : s ∈ treesOn q)
    (h : IsStrictMin p s) : cfClass p q = .cycle s := by
  have hno : ¬ ∃ s ∈ treesOn q, IsT1Strict p s := fun ⟨s', hs', h'⟩ =>
    not_isT1Strict_of_isStrictMin h h' ((mem_treesOn.1 hs).trans (mem_treesOn.1 hs').symm)
  have hex : ∃ s ∈ treesOn q, IsStrictMin p s := ⟨s, hs, h⟩
  rw [cfClass, dite_eq_right hno, dite_eq_left hex]
  congr 1
  exact IsStrictMin.unique hex.choose_spec.2 h
    ((mem_treesOn.1 hex.choose_spec.1).trans (mem_treesOn.1 hs).symm)

theorem cfClass_eq_star {p : QuartetTree X → ℝ} {q : Finset X} (h : ∀ r ∈ treesOn q, p r = 1 / 3) :
    cfClass p q = .star := by
  have hmem : ∀ {s r : QuartetTree X}, s ∈ treesOn q → r ∈ s.alternatives → r ∈ treesOn q := fun hs hr =>
    mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs))
  have hno : ¬ ∃ s ∈ treesOn q, IsT1Strict p s := by
    rintro ⟨s, hs, h', -⟩
    obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
    have hr : r₁ ∈ s.alternatives := by rw [ha]; simp
    exact (h' r₁ hr).ne ((h r₁ (hmem hs hr)).trans (h s hs).symm)
  have hno' : ¬ ∃ s ∈ treesOn q, IsStrictMin p s := by
    rintro ⟨s, hs, h'⟩
    obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
    have hr : r₁ ∈ s.alternatives := by rw [ha]; simp
    exact (h' r₁ hr).ne ((h s hs).trans (h r₁ (hmem hs hr)).symm)
  rw [cfClass, dite_eq_right hno, dite_eq_right hno']

/-- A concordance factor off model T3 has a topology of strictly least value: the two smallest entries are not equal.
This is what makes the "3 triangular regions" of Figure 4 (R) cover the complement of the three half-lines. -/
theorem exists_isStrictMin_of_not_isT3Null {p : QuartetTree X → ℝ} {q : Finset X} (hq : q.card = 4)
    (h : ¬ IsT3Null p q) : ∃ s ∈ treesOn q, IsStrictMin p s := by
  have hne : (treesOn q).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq]
    norm_num
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ p hne
  have hst : s.taxa = q := mem_treesOn.1 hs
  obtain ⟨r₁, r₂, hne₂, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
  have hmem : ∀ {r : QuartetTree X}, r ∈ s.alternatives → r ∈ treesOn q := fun hr =>
    mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans hst)
  have hr₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
  have hr₂ : r₂ ∈ s.alternatives := by rw [ha]; simp
  have hneq : p r₁ ≠ p r₂ := by
    intro heq
    refine h ⟨s, hs, fun r hr => hmax r (hmem hr), fun r hr r' hr' => ?_⟩
    rw [ha] at hr hr'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr hr'
    rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> first | rfl | exact heq | exact heq.symm
  have key : ∀ {r r' : QuartetTree X}, s.alternatives = {r, r'} → r ∈ treesOn q → p r < p r' →
      ∃ s ∈ treesOn q, IsStrictMin p s := by
    intro r r' ha' hrq hlt
    refine ⟨r, hrq, fun u hu => ?_⟩
    have hrs : r ∈ s.alternatives := by rw [ha']; simp
    have hr's : r' ∈ s.alternatives := by rw [ha']; simp
    have hle := hmax r' (hmem hr's)
    rcases other_alternative ha' hu with rfl | rfl
    · exact hlt.trans_le hle
    · exact hlt
  rcases lt_or_gt_of_ne hneq with hlt | hlt
  · exact key ha (hmem hr₁) hlt
  · exact key (by rw [ha, Finset.pair_comm]) (hmem hr₂) hlt

/-- The three cases of a concordance factor summing to one: the centroid; strictly on a half-line; off model T3. -/
theorem cf_trichotomy {p : QuartetTree X → ℝ} {q : Finset X} (hq : q.card = 4) (hsum : ∑ r ∈ treesOn q, p r = 1) :
    (∀ r ∈ treesOn q, p r = 1 / 3) ∨ (∃ s ∈ treesOn q, IsT1Strict p s) ∨
      (¬ IsT3Null p q ∧ ∃ s ∈ treesOn q, IsStrictMin p s) := by
  by_cases hT : IsT3Null p q
  · obtain ⟨s, hs, hle, heq⟩ := hT
    by_cases hstrict : ∀ r ∈ s.alternatives, p r < p s
    · exact Or.inr (Or.inl ⟨s, hs, hstrict, heq⟩)
    · refine Or.inl ?_
      push Not at hstrict
      obtain ⟨u, hu, hsu⟩ := hstrict
      have hus : p u = p s := le_antisymm (hle u hu) hsu
      have hst : s.taxa = q := mem_treesOn.1 hs
      obtain ⟨r₁, r₂, hne₂, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
      have hT : treesOn q = {s, r₁, r₂} := by
        ext r
        simp only [mem_treesOn, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hr
          by_cases hrs : r = s
          · exact Or.inl hrs
          · have : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hr.trans hst.symm, hrs⟩
            rw [ha] at this
            simpa using Or.inr (by simpa using this)
        · rintro (rfl | rfl | rfl)
          · exact hst
          · exact (QuartetTree.mem_alternatives.1 (by rw [ha]; simp : r ∈ s.alternatives)).1.trans hst
          · exact (QuartetTree.mem_alternatives.1 (by rw [ha]; simp : r ∈ s.alternatives)).1.trans hst
      have hr₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
      have hr₂ : r₂ ∈ s.alternatives := by rw [ha]; simp
      have h₁ : p r₁ = p s := (heq r₁ hr₁ u hu).trans hus
      have h₂ : p r₂ = p s := (heq r₂ hr₂ u hu).trans hus
      have hsr₁ : s ≠ r₁ := (QuartetTree.mem_alternatives.1 hr₁).2.symm
      have hsr₂ : s ≠ r₂ := (QuartetTree.mem_alternatives.1 hr₂).2.symm
      rw [hT, Finset.sum_insert (by simp [hsr₁, hsr₂]), Finset.sum_pair hne₂, h₁, h₂] at hsum
      have hval : p s = 1 / 3 := by linarith
      intro r hr
      rw [hT] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact hval
      · exact h₁.trans hval
      · exact h₂.trans hval
  · exact Or.inr (Or.inr ⟨hT, exists_isStrictMin_of_not_isT3Null hq hT⟩)

/-! ### The statistics as printed -/

/-- The display "`λ = 2 (m₁ log(m₁/m) + m₂ log(m₂/m) + m₃ log(m₃/m) - m log(1/3))`" (line 2038) is the star statistic
`starStat`. -/
theorem starStat_eq_printed {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) (q : Finset X) {m : ℝ}
    (hm : ∑ r ∈ treesOn q, c r = m) :
    starStat c q = 2 * (∑ r ∈ treesOn q, c r * Real.log (c r / m) - m * Real.log (1 / 3)) := by
  have hm₀ : 0 ≤ m := hm ▸ Finset.sum_nonneg fun r _ => hc r
  rcases hm₀.eq_or_lt with hm₁ | hm₁
  · have hz : ∀ r ∈ treesOn q, c r = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hc r).1 (hm.trans hm₁.symm)
    rw [starStat, hm, ← hm₁, Finset.sum_eq_zero fun r hr => by rw [hz r hr, zero_mul],
      Finset.sum_eq_zero fun r hr => by rw [hz r hr, zero_mul]]
    simp
  · have hterm : ∀ r ∈ treesOn q, c r * Real.log (c r / m) = c r * Real.log (c r) - c r * Real.log m := by
      intro r _
      rcases (hc r).eq_or_lt with h0 | h0
      · simp [← h0]
      · rw [Real.log_div h0.ne' hm₁.ne']
        ring
    rw [starStat, hm, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, hm,
      Real.log_div hm₁.ne' (by norm_num), one_div, Real.log_inv]
    ring

/-- The limit `d` of the statistic in the source (line 2191): the statistic of the line of `s`, in the form printed
there. -/
theorem lineStat_eq_printed (c : QuartetTree X → ℝ) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (ha : s.alternatives = {r₁, r₂}) :
    lineStat c s = 2 * (c r₁ * Real.log (c r₁) + c r₂ * Real.log (c r₂) -
      (c r₁ + c r₂) * Real.log ((c r₁ + c r₂) / 2)) := by
  rw [lineStat, ha, Finset.sum_pair hne, Finset.sum_pair hne]
  by_cases h0 : c r₁ + c r₂ = 0
  · rw [h0]
    simp
  · rw [Real.log_div h0 (by norm_num)]
    ring

/-- The display of the source for the statistic of the second test (lines 2113-2129), with `m_max` the count of `s`
and `m` the total, is the statistic `t3Stat` of the T3 test. -/
theorem t3Stat_eq_printed {c : QuartetTree X → ℝ} (hc : ∀ r, 0 ≤ c r) {s r₁ r₂ : QuartetTree X} (hne : r₁ ≠ r₂)
    (ha : s.alternatives = {r₁, r₂}) (hmax : ∀ r ∈ s.alternatives, c r ≤ c s) {m : ℝ}
    (hm : c s + c r₁ + c r₂ = m) :
    t3Stat c s.taxa = 2 * (c s * Real.log (c s / m) + c r₁ * Real.log (c r₁ / m) + c r₂ * Real.log (c r₂ / m) -
      c s * Real.log (c s / m) - (m - c s) * Real.log ((m - c s) / (2 * m))) := by
  rw [QuartetTests.t3Stat_eq_lineStat_of_max hc hmax, lineStat_eq_printed c hne ha]
  have hs := hc s
  have h₁ := hc r₁
  have h₂ := hc r₂
  have hms : m - c s = c r₁ + c r₂ := by linarith
  rw [hms]
  rcases (add_nonneg (add_nonneg hs h₁) h₂).eq_or_lt with hz | hpos
  · have hz₁ : c r₁ = 0 := by linarith
    have hz₂ : c r₂ = 0 := by linarith
    simp [hz₁, hz₂]
  · have hm₀ : 0 < m := hm ▸ hpos
    have hterm : ∀ x : ℝ, 0 ≤ x → x * Real.log (x / m) = x * Real.log x - x * Real.log m := by
      intro x hx
      rcases hx.eq_or_lt with h0 | h0
      · simp [← h0]
      · rw [Real.log_div h0.ne' hm₀.ne']
        ring
    have hlast : (c r₁ + c r₂) * Real.log ((c r₁ + c r₂) / (2 * m)) =
        (c r₁ + c r₂) * Real.log ((c r₁ + c r₂) / 2) - (c r₁ + c r₂) * Real.log m := by
      by_cases h0 : c r₁ + c r₂ = 0
      · simp [h0]
      · rw [← div_div, Real.log_div (div_ne_zero h0 (by norm_num)) hm₀.ne']
        ring
    rw [hterm _ h₁, hterm _ h₂, hlast]
    ring

/-- The T3 statistic scales with the counts. -/
theorem t3Stat_const_mul {a : ℝ} (ha : 0 < a) (c : QuartetTree X → ℝ) (q : Finset X) :
    t3Stat (fun r => a * c r) q = a * t3Stat c q := by
  unfold t3Stat
  rw [Real.mul_iInf_of_nonneg ha.le]
  exact iInf_congr fun s => QuartetTests.t1Stat_const_mul ha c s.val

/-- The T3 statistic is continuous at a nonnegative point, among nonnegative points: near `p`, a topology of largest
value is a topology of largest value of `p`, and the statistic is the statistic of its line
(`QuartetTests.t3Stat_eq_lineStat_of_max`). This is what "the continuous mapping theorem" of the source uses for `Y_m`
(line 2168). -/
theorem eventually_abs_t3Stat_sub_lt {p : QuartetTree X → ℝ} (hp : ∀ r, 0 ≤ p r) {q : Finset X} (hq : q.card = 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 p, (∀ r, 0 ≤ x r) → |t3Stat x q - t3Stat p q| < ε := by
  have h₁ : ∀ᶠ x in 𝓝 p, ∀ r ∈ treesOn q, |lineStat x r - lineStat p r| < ε := by
    rw [Finset.eventually_all]
    intro r _
    have := (QuartetTests.continuous_lineStat (X := X) r).tendsto p
    have h := this.sub_const (lineStat p r)
    rw [sub_self] at h
    filter_upwards [h.abs.eventually (by simpa using gt_mem_nhds hε)] with x hx using hx
  have h₂ : ∀ᶠ x in 𝓝 p, ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, p r < p r' → x r < x r' := by
    rw [Finset.eventually_all]
    intro r _
    rw [Finset.eventually_all]
    intro r' _
    by_cases hlt : p r < p r'
    · filter_upwards [((continuous_apply r).tendsto p).eventually_lt ((continuous_apply r').tendsto p) hlt]
        with x hx _ using hx
    · exact Eventually.of_forall fun x h => absurd h hlt
  filter_upwards [h₁, h₂] with x hx₁ hx₂ hnn
  have hne : (treesOn q).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq]
    norm_num
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image _ x hne
  have hut : u.taxa = q := mem_treesOn.1 hu
  have hmem : ∀ {r : QuartetTree X}, r ∈ u.alternatives → r ∈ treesOn q := fun hr =>
    mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans hut)
  have hx : t3Stat x q = lineStat x u := by
    rw [← hut]
    exact QuartetTests.t3Stat_eq_lineStat_of_max hnn fun r hr => hmax r (hmem hr)
  have hp' : t3Stat p q = lineStat p u := by
    rw [← hut]
    refine QuartetTests.t3Stat_eq_lineStat_of_max hp fun r hr => ?_
    by_contra hlt
    exact absurd (hmax r (hmem hr)) (not_le.2 (hx₂ u hu r (hmem hr) (not_le.1 hlt)))
  rw [hx, hp']
  exact hx₁ u hu

/-- Off model T3, the limit of the statistic is positive: `d > 0` (line 2191). -/
theorem t3Stat_pos_of_not_isT3Null {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}
    (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X} (hq : q.card = 4)
    (h : ¬ IsT3Null (displayCF dist sides) q) : 0 < t3Stat (displayCF dist sides) q := by
  obtain ⟨u, hu, he⟩ := QuartetTests.exists_t3Stat_eq (displayCF dist sides) hq
  obtain ⟨d, hd0, hF⟩ := QuartetTests.exists_lt_t1Stat hd hs (s := u) fun hn => h ⟨u, hu, hn⟩
  rw [he]
  exact hd0.trans hF.self_of_nhds

/-! ### Step 2 on a sample -/

section Sample

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

/-- The limit of the statistic, with its error: "`Y_m` converges in probability to `d`" (line 2168), for `Y_m` the
statistic over `m`. -/
theorem tendsto_t3Stat_near (hd : IsDist dist) {q : Finset X} (hq : q.card = 4) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => iidProb dist n fun ω =>
      n * (t3Stat (displayCF dist sides) q - ε) < t3Stat (quartetCount sides ω) q ∧
        t3Stat (quartetCount sides ω) q < n * (t3Stat (displayCF dist sides) q + ε)) atTop (𝓝 1) := by
  have hF := eventually_abs_t3Stat_sub_lt (QuartetTests.displayCF_nonneg hd (sides := sides)) hq hε
  refine tendsto_iidProb_of_imp hd ?_ (QuartetTests.tendsto_iidProb_freq hd hF)
  filter_upwards [eventually_gt_atTop 0] with n hn0 ω hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc := QuartetTests.quartetCount_nonneg (sides := sides) ω
  have hab := abs_lt.1 (hω fun r => div_nonneg (hc r) hn'.le)
  have hcmul : quartetCount sides ω = fun r => (n : ℝ) * (quartetCount sides ω r / n) := by
    funext r
    field_simp
  rw [hcmul, t3Stat_const_mul hn']
  constructor
  · exact mul_lt_mul_of_pos_left (by linarith [hab.1]) hn'
  · exact mul_lt_mul_of_pos_left (by linarith [hab.2]) hn'

/-- "`P(λ > md/2) > 1 - ε`" (lines 2193-2196): off model T3, the statistic exceeds half its limit, with probability
tending to one. -/
theorem tendsto_half_lt_t3Stat (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ¬ IsT3Null (displayCF dist sides) q) :
    Tendsto (fun n : ℕ => iidProb dist n fun ω =>
      n * (t3Stat (displayCF dist sides) q / 2) < t3Stat (quartetCount sides ω) q) atTop (𝓝 1) := by
  have hpos := t3Stat_pos_of_not_isT3Null hd hs hq h
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_t3Stat_near (sides := sides) hd hq (half_pos hpos))
  have := hω.1
  rwa [sub_half] at this

/-- The first test at a concordance factor off the centroid: "for any significance level `0 < β < 1`, the null
hypothesis will be rejected" (lines 2082-2086). The source's argument, `P(λ > mc/2) → 1`, is
`QuartetTests.starStat_growth`. It also holds for levels that tend to zero, provided `log(1/β_n) = o(n)`. -/
theorem tendsto_starPValue_lt (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ¬ ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) {β : ℕ → ℝ} (hβ : ∀ n, 0 < β n)
    (hβlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω => starPValue .lrt (quartetCount sides ω) q < β n) atTop (𝓝 1) := by
  have hb : Tendsto (fun n : ℕ => -2 * Real.log (β n) / n) atTop (𝓝 0) := by
    have := hβlog.const_mul (-2)
    rw [mul_zero] at this
    exact this.congr fun n => by ring
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (QuartetTests.starStat_growth .lrt hd hs hq h hb)
  have he : Real.exp (-(-2 * Real.log (β n)) / 2) = β n := by
    rw [show -(-2 * Real.log (β n)) / 2 = Real.log (β n) by ring, Real.exp_log (hβ n)]
  rw [he] at hω
  exact hω

/-- A constant level has `log(1/β) = o(n)`. -/
theorem tendsto_log_const_div (β : ℝ) : Tendsto (fun n : ℕ => Real.log β / n) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

/-- The first test at the centroid: there its p-value is asymptotically uniform, so at levels tending to zero it does
not reject, with probability tending to one. The source's Theorem 36 takes a fixed `β`, and this case does not arise
in its argument, which says that `p_i ≠ 1/3` (see `not_tendsto_of_centroid`). -/
theorem tendsto_le_starPValue (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) {β : ℕ → ℝ}
    (hβ₀ : Tendsto β atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω => β n ≤ starPValue .lrt (quartetCount sides ω) q) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha =>
    Eventually.of_forall fun n => (iidProb_le_one hd n _).trans_lt ha⟩
  set ε := min 1 ((1 - a) / 2) with hε
  have hgap : 0 < 1 - a := sub_pos.2 ha
  have hε₀ : 0 < ε := lt_min one_pos (half_pos hgap)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hε₂ : ε ≤ (1 - a) / 2 := min_le_right _ _
  have hu := QuartetTests.starPValue_asymptoticallyUniform .lrt hd hs hq h ε hε₀.le hε₁
  filter_upwards [hu.eventually (gt_mem_nhds (show ε < ε + (1 - a) / 4 by linarith)),
    hβ₀.eventually (gt_mem_nhds hε₀)] with n hn₁ hn₂
  have hle : iidProb dist n (fun ω => ¬ β n ≤ starPValue .lrt (quartetCount sides ω) q) ≤
      iidProb dist n fun ω => starPValue .lrt (quartetCount sides ω) q ≤ ε :=
    iidProb_mono hd fun ω hω => (not_le.1 hω).le.trans hn₂.le
  rw [iidProb_not hd] at hle
  linarith

/-- The second test at a concordance factor strictly on a half-line: the topology of largest count is the true one,
and the test does not reject at any levels tending to zero: "it is enough to choose any sequence of significance
levels with `α_m → 0`" (lines 2096-2101). -/
theorem tendsto_maxCount_t3 (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {s : QuartetTree X}
    (hstrict : IsT1Strict (displayCF dist sides) s)
    (hpos : ∀ r, 0 < displayCF dist sides r) {α : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    {mlT : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT) :
    Tendsto (fun n => iidProb dist n fun ω =>
      mlT (quartetCount sides ω) s.taxa = s ∧ α n ≤ t3PValue (quartetCount sides ω) s) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (QuartetTests.t3Test_null hd hs hstrict (fun r _ => hpos r) hα₀)
  obtain ⟨h₁, h₂⟩ := hω
  refine ⟨?_, h₂⟩
  have hc := QuartetTests.quartetCount_nonneg (sides := sides) ω
  obtain ⟨hm, hmax⟩ := hmlT (quartetCount sides ω) s.taxa s.card_taxa
  by_contra hne
  have hrt := mem_treesOn.1 hm
  have halt := QuartetTree.mem_alternatives.2 ⟨hrt, hne⟩
  have hle := QuartetTests.t1Stat_le_t1Stat_of_max hc
    (s := mlT (quartetCount sides ω) s.taxa) (r := s)
    (fun u hu => hmax u (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hu).1.trans hrt)))
    (mem_treesOn.2 hrt.symm)
  exact absurd (h₁ _ halt) (not_lt.2 hle)

/-- By the law of large numbers, the topology of least count is the one of strictly least concordance factor. -/
theorem tendsto_minCount (hd : IsDist dist) {s : QuartetTree X} (hmin : IsStrictMin (displayCF dist sides) s)
    {mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb dist n fun ω => mlC (quartetCount sides ω) s.taxa = s) atTop (𝓝 1) := by
  have hF : ∀ᶠ x in 𝓝 (displayCF dist sides), ∀ r ∈ s.alternatives, x s < x r := by
    rw [Finset.eventually_all]
    intro r hr
    exact ((continuous_apply s).tendsto _).eventually_lt ((continuous_apply r).tendsto _) (hmin r hr)
  refine tendsto_iidProb_of_imp hd ?_ (QuartetTests.tendsto_iidProb_freq hd hF)
  filter_upwards [eventually_gt_atTop 0] with n hn0 ω hω
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨hm, hle⟩ := hmlC (quartetCount sides ω) s.taxa s.card_taxa
  by_contra hne
  have h₁ := hω _ (QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hm, hne⟩)
  exact absurd ((div_lt_div_iff_of_pos_right hn').1 h₁) (not_lt.2 (hle s (mem_treesOn.2 rfl)))

/-- The levels `α` make the second test reject off its null, with probability tending to one. -/
def RejectsOffNull (dist : Γ → ℝ) (sides : Γ → Finset (Finset X)) (α : ℕ → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → ¬ IsT3Null (displayCF dist sides) q →
    Tendsto (fun n => iidProb dist n fun ω => ∀ u ∈ treesOn q, t3PValue (quartetCount sides ω) u < α n)
      atTop (𝓝 1)

/-- Levels with `log(1/α_n) = o(n)` reject off the null: the argument of ECToBlob's Theorem 8.2
(`QuartetTests.t3Test_rejects`). -/
theorem rejectsOffNull_of_log (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {α : ℕ → ℝ}
    (hα : ∀ n, 0 < α n) (hαlog : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0)) :
    RejectsOffNull dist sides α := fun _ hq h => QuartetTests.t3Test_rejects hd hs hq h hα hαlog

/-- On a set of four taxa, Step 2 gives the population value, with probability tending to one. The case of the
centroid needs levels `β_n → 0`. -/
theorem tendsto_classify_eq_cfClass_at (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides)
    (hpos : ∀ r, 0 < displayCF dist sides r) {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : RejectsOffNull dist sides α) (hβ : ∀ n, 0 < β n)
    (hβlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0))
    (hcen : TINNiK.NoCentroidCF (displayCF dist sides) ∨ Tendsto β atTop (𝓝 0))
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) {q : Finset X} (hq : q.card = 4) :
    Tendsto (fun n => iidProb dist n fun ω =>
      classify mlT mlC (α n) (β n) (quartetCount sides ω) q = cfClass (displayCF dist sides) q) atTop (𝓝 1) := by
  rcases cf_trichotomy hq (QuartetTests.sum_displayCF_treesOn hd hs hq) with
    huni | ⟨s, hsq, hstrict⟩ | ⟨hnull, s, hsq, hmin⟩
  · rcases hcen with hno | hβ₀
    · exact absurd huni (hno q hq)
    · rw [cfClass_eq_star huni]
      refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
        (tendsto_le_starPValue hd hs hq huni hβ₀)
      rw [classify, ite_eq_left hω]
  · have hst : s.taxa = q := mem_treesOn.1 hsq
    subst hst
    have hoff : ¬ ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3 := by
      intro hall
      obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
      have hr : r₁ ∈ s.alternatives := by rw [ha]; simp
      exact (hstrict.1 r₁ hr).ne ((hall r₁ (QuartetTests.mem_treesOn_taxa_of_mem_alternatives hr)).trans
        (hall s hsq).symm)
    rw [cfClass_eq_tree hsq hstrict]
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
      (tendsto_iidProb_and hd (tendsto_starPValue_lt hd hs hq hoff hβ hβlog)
        (tendsto_maxCount_t3 hd hs hstrict hpos hα₀ hmlT))
    obtain ⟨h₁, h₂, h₃⟩ := hω
    rw [classify, ite_eq_right (not_le.2 h₁), h₂, ite_eq_left h₃]
  · have hst : s.taxa = q := mem_treesOn.1 hsq
    subst hst
    have hoff : ¬ ∀ r ∈ treesOn s.taxa, displayCF dist sides r = 1 / 3 := by
      intro hall
      obtain ⟨r₁, r₂, -, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
      have hr : r₁ ∈ s.alternatives := by rw [ha]; simp
      exact (hmin r₁ hr).ne ((hall s hsq).trans
        (hall r₁ (QuartetTests.mem_treesOn_taxa_of_mem_alternatives hr)).symm)
    rw [cfClass_eq_cycle hsq hmin]
    refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
      (tendsto_iidProb_and hd (tendsto_starPValue_lt hd hs hq hoff hβ hβlog)
        (tendsto_iidProb_and hd (hrej _ hq hnull) (tendsto_minCount hd hmin hmlC)))
    obtain ⟨h₁, h₂, h₃⟩ := hω
    rw [classify, ite_eq_right (not_le.2 h₁), ite_eq_right (not_le.2 (h₂ _ (hmlT _ _ hq).1)), h₃]

/-- **Step 2 is consistent for its population value**: on all sets of four taxa at once, with probability tending to
one, for levels `α_n → 0` that reject off the null, and levels `β_n` with `log(1/β_n) = o(n)`, tending to zero when a
concordance factor is at the centroid. -/
theorem tendsto_classify_eq_cfClass (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides)
    (hpos : ∀ r, 0 < displayCF dist sides r) {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : RejectsOffNull dist sides α) (hβ : ∀ n, 0 < β n)
    (hβlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0))
    (hcen : TINNiK.NoCentroidCF (displayCF dist sides) ∨ Tendsto β atTop (𝓝 0))
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb dist n fun ω => ∀ q : Finset X, q.card = 4 →
      classify mlT mlC (α n) (β n) (quartetCount sides ω) q = cfClass (displayCF dist sides) q) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω q hq => hω ⟨q, hq⟩)
    (tendsto_iidProb_forall hd (ι := {q : Finset X // q.card = 4})
      (fun q n ω => classify mlT mlC (α n) (β n) (quartetCount sides ω) q.val =
        cfClass (displayCF dist sides) q.val)
      fun q => tendsto_classify_eq_cfClass_at hd hs hpos hα₀ hrej hβ hβlog hcen hmlT hmlC q.property)

/-! ### The levels of the proof of Theorem 36 -/

private theorem tendsto_chiSqTwoTail_mul {d : ℝ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => chiSqTwoTail (m * d)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) * d / 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hd).atTop_div_const (by norm_num)
  refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).congr fun m => ?_
  simp [chiSqTwoTail, neg_div]

/-- The level `α'_m` on a set of four taxa off the null, as in the source's "Let `α'_m = P(W_m > md/2)`" (lines
2195-2196), rejects there with probability tending to one.

Departure from the paper: the source's `α'_m` is the tail of the law `W_m` of the test. That law depends on the
parameter `φ` of the null, and the p-value uses its estimate, which depends on the data, so `P(W_m > md/2)` is not a
number. Here `α'_m` is the upper bound `P(χ²₂ > md/2)` of the tail for every `φ`
(`QuartetTests.t3Tail_le_chiSqTwoTail`). The argument is otherwise the source's. -/
theorem tendsto_t3PValue_lt_level (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ¬ IsT3Null (displayCF dist sides) q) :
    Tendsto (fun m : ℕ => iidProb dist m fun ω => ∀ u ∈ treesOn q, t3PValue (quartetCount sides ω) u <
      chiSqTwoTail (m * (t3Stat (displayCF dist sides) q / 2))) atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω u hu => ?_)
    (tendsto_half_lt_t3Stat hd hs hq h)
  have h₁ := QuartetTests.t3PValue_le_chiSqTwoTail (QuartetTests.quartetCount_nonneg (sides := sides) ω) u
  rw [mem_treesOn.1 hu] at h₁
  refine h₁.trans_lt (Real.exp_lt_exp.2 ?_)
  linarith

/-- **The levels of the proof of Theorem 36** (lines 2195-2211).

Departure from the paper: the source takes "`α_m` to be the minimum of the `α'_m`" over the non-tree-like sets of four
taxa (line 2207). That is an error: a level rejects when the p-value is below it, so rejecting on all those sets needs
a level at least each `α'_m`, and at the minimum the test may not reject (`not_rejects_at_minimum`). Here `α_m` is the
maximum, with `P(χ²₂ > m)` added so that the maximum is over a nonempty set. This is how `TINNiK.exists_levels_t3`
chooses. It tends to zero like the minimum, and everything else in the proof stands. -/
theorem exists_levels (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) :
    ∃ α : ℕ → ℝ, Tendsto α atTop (𝓝 0) ∧ (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧
      RejectsOffNull dist sides α := by
  set p := displayCF dist sides with hp
  let Q : Finset (Finset X) := univ.filter fun q => q.card = 4 ∧ ¬ IsT3Null p q
  have hQ : ∀ q ∈ Q, 0 < t3Stat p q / 2 := fun q hq => by
    obtain ⟨hq4, hn⟩ := (mem_filter.mp hq).2
    exact half_pos (t3Stat_pos_of_not_isT3Null hd hs hq4 hn)
  let α : ℕ → ℝ := fun m => Q.fold max (chiSqTwoTail (m * 1)) fun q => chiSqTwoTail (m * (t3Stat p q / 2))
  have hle : ∀ m : ℕ, ∀ q ∈ Q, chiSqTwoTail (m * (t3Stat p q / 2)) ≤ α m := fun m q hq =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, le_rfl⟩)
  have hbase : ∀ m : ℕ, chiSqTwoTail (m * 1) ≤ α m := fun m =>
    (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  have hpos : ∀ t : ℝ, 0 < chiSqTwoTail t := fun t => Real.exp_pos _
  have hlt1 : ∀ {m : ℕ} {d : ℝ}, 1 ≤ m → 0 < d → chiSqTwoTail (m * d) < 1 := by
    intro m d hm hd0
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    unfold chiSqTwoTail
    rw [Real.exp_lt_one_iff]
    have := mul_pos hm' hd0
    linarith
  refine ⟨α, ?_, fun m => (hpos _).trans_le (hbase m), fun m hm => ?_, ?_⟩
  · have hsum : Tendsto (fun m : ℕ => chiSqTwoTail (m * 1) + ∑ q ∈ Q, chiSqTwoTail (m * (t3Stat p q / 2)))
        atTop (𝓝 0) := by
      have := (tendsto_chiSqTwoTail_mul (d := 1) one_pos).add
        (tendsto_finsetSum Q fun q hq => tendsto_chiSqTwoTail_mul (hQ q hq))
      simpa using this
    refine squeeze_zero (fun m => (hpos _).le.trans (hbase m)) (fun m => ?_) hsum
    refine (Finset.fold_max_le _).mpr ⟨?_, fun q hq => ?_⟩
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (hpos _).le)
    · exact (Finset.single_le_sum (f := fun q => chiSqTwoTail (m * (t3Stat p q / 2)))
        (fun _ _ => (hpos _).le) hq).trans (le_add_of_nonneg_left (hpos _).le)
  · exact (Finset.fold_max_lt _).mpr ⟨hlt1 hm one_pos, fun q hq => hlt1 hm (hQ q hq)⟩
  · intro q hq4 hn
    have hq : q ∈ Q := mem_filter.mpr ⟨mem_univ _, hq4, hn⟩
    exact tendsto_iidProb_of_imp hd
      (Eventually.of_forall fun m ω hω u hu => (hω u hu).trans_le (hle m q hq))
      (tendsto_t3PValue_lt_level hd hs hq4 hn)

end Sample

/-! ### The quartet distance compared with TINNiK's -/

/-- `C` is a class of a set `q` of four taxa, with its quartet tree on `q`. -/
def IsClassOn (C : QuartetClass X) (q : Finset X) : Prop :=
  match C with
  | .star => True
  | .tree s => s ∈ treesOn q
  | .cycle s => s ∈ treesOn q

theorem classify_isClassOn {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X}
    (hmlT : IsMaxCountSelection mlT) (hmlC : IsMinCountSelection mlC) (α β : ℝ) (c : QuartetTree X → ℝ)
    {q : Finset X} (hq : q.card = 4) : IsClassOn (classify mlT mlC α β c q) q := by
  unfold classify
  split_ifs
  · trivial
  · exact (hmlT c q hq).1
  · exact (hmlC c q hq).1

/-- The sets judged unresolved by TINNiK's reading of a classification: its B-quartets, the star trees and the
4-cycles alike. -/
def unresolved (cl : Finset X → QuartetClass X) : Set (Finset X) :=
  {q | cl q = .star ∨ ∃ s, cl q = .cycle s}

/-- The quartet trees of a classification. -/
def resolved (cl : Finset X → QuartetClass X) : Set (QuartetTree X) := {s | cl s.taxa = .tree s}

/-- The distance as a count, when `ρ` is an indicator. -/
theorem nanuqDistance_eq_quartetDistance_of_rho {cl : Finset X → QuartetClass X} {Bq : Set (Finset X)}
    {τ : Set (QuartetTree X)} {x y : X}
    (h : ∀ q : Finset X, q.card = 4 → x ∈ q → y ∈ q →
      rho (cl q) x y = if q ∈ Bq ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y then 1 else 0) :
    nanuqDistance cl x y = quartetDistance Bq τ x y := by
  unfold nanuqDistance quartetDistance
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, ↓reduceIte]
    congr 3
    rw [Finset.sum_congr rfl fun q hq => h q (mem_filter.mp hq).2.1 (mem_filter.mp hq).2.2.1
      (mem_filter.mp hq).2.2.2, Finset.sum_boole, Finset.filter_filter]
    simp only [and_assoc]

/-- **The NANUQ and TINNiK quartet distances differ exactly on 4-cycles.** The distance of TINNiK (Rhodes 2020) counts
a set in which `x, y` are not a cherry with weight `1`, and an unresolved set as `1`. NANUQ gives `1/2` to the
adjacent taxa of a 4-cycle (Definition 20). So the two differ at `x ≠ y` by the number of sets judged 4-cycles with
`x, y` adjacent. -/
theorem quartetDistance_sub_nanuqDistance {cl : Finset X → QuartetClass X}
    (hcl : ∀ q : Finset X, q.card = 4 → IsClassOn (cl q) q) {x y : X} (hxy : x ≠ y) :
    quartetDistance (unresolved cl) (resolved cl) x y - nanuqDistance cl x y =
      ((univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧
        ∃ s, cl q = .cycle s ∧ Separated s x y).card : ℝ) := by
  set F := univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q with hF
  have hterm : ∀ q ∈ F, (if q ∈ unresolved cl ∨ ∃ s ∈ resolved cl, s.taxa = q ∧ Separated s x y then (1 : ℝ) else 0) -
      rho (cl q) x y = (1 / 2) * (if ∃ s, cl q = .cycle s ∧ Separated s x y then (1 : ℝ) else 0) := by
    intro q hq
    have hq4 := (mem_filter.mp hq).2.1
    have hclq := hcl q hq4
    rcases hcq : cl q with _ | s | s
    · have : q ∈ unresolved cl := Or.inl hcq
      simp [this, rho]
    · have hst : s.taxa = q := by
        rw [hcq] at hclq
        exact mem_treesOn.1 hclq
      have hnot : q ∉ unresolved cl := by
        rintro (h | ⟨s', h⟩) <;> simp [hcq] at h
      have hiff : (∃ s' ∈ resolved cl, s'.taxa = q ∧ Separated s' x y) ↔ Separated s x y := by
        constructor
        · rintro ⟨s', hs', ht, hsep⟩
          have : cl s'.taxa = .tree s' := hs'
          rw [ht, hcq] at this
          rw [QuartetClass.tree.inj this]
          exact hsep
        · intro hsep
          refine ⟨s, ?_, hst, hsep⟩
          change cl s.taxa = .tree s
          rw [hst, hcq]
      simp [hnot, hiff, rho]
    · have : q ∈ unresolved cl := Or.inr ⟨s, hcq⟩
      by_cases hsep : Separated s x y
      · simp [this, rho, hsep]
        norm_num
      · simp [this, rho, hsep]
  have hxy' : ¬ x = y := hxy
  have hcount : ∑ q ∈ F, (if q ∈ unresolved cl ∨ ∃ s ∈ resolved cl, s.taxa = q ∧ Separated s x y then (1 : ℝ) else 0) =
      ((univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧
        (q ∈ unresolved cl ∨ ∃ s ∈ resolved cl, s.taxa = q ∧ Separated s x y)).card : ℝ) := by
    rw [Finset.sum_boole, hF, Finset.filter_filter]
    simp only [and_assoc]
  have hcount' : ∑ q ∈ F, (if ∃ s, cl q = .cycle s ∧ Separated s x y then (1 : ℝ) else 0) =
      ((univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧
        ∃ s, cl q = .cycle s ∧ Separated s x y).card : ℝ) := by
    rw [Finset.sum_boole, hF, Finset.filter_filter]
    simp only [and_assoc]
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount, hcount'] at hsum
  simp only [quartetDistance, nanuqDistance, hxy', ↓reduceIte, ← hF]
  linarith

/-- On a classification with no 4-cycle, the NANUQ distance is TINNiK's. "Guided by the results in [5] on quartet
distances for non-binary trees, we set `ρ_xy = 1` if `Q̃` is a star tree" (lines 1964-1968). -/
theorem nanuqDistance_eq_quartetDistance {cl : Finset X → QuartetClass X}
    (hcl : ∀ q : Finset X, q.card = 4 → IsClassOn (cl q) q) (hno : ∀ q : Finset X, q.card = 4 → ∀ s, cl q ≠ .cycle s)
    {x y : X} : nanuqDistance cl x y = quartetDistance (unresolved cl) (resolved cl) x y := by
  by_cases hxy : x = y
  · simp [nanuqDistance, quartetDistance, hxy]
  have h := quartetDistance_sub_nanuqDistance hcl hxy
  have hz : (univ.filter fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧
      ∃ s, cl q = .cycle s ∧ Separated s x y) = ∅ := by
    refine Finset.filter_false_of_mem ?_
    rintro q - ⟨hq, -, -, s, hs, -⟩
    exact hno q hq s hs
  rw [hz] at h
  simp only [Finset.card_empty, Nat.cast_zero] at h
  linarith

/-- The class of a set of four taxa on a tree `T`: the quartet tree that it displays there, or a star tree. -/
def treeClass (T : Finset (Finset X)) (q : Finset X) : QuartetClass X :=
  if h : ∃ s ∈ treesOn q, Displays T s then .tree h.choose else .star

/-- **The distance on a tree** (the source's Theorem 17, from Rhodes 2020, and "if `N⁻ = T` is a tree, the definition
of `d_{Q,N⁻}(x, y)` agrees with equation (2)", line 1133): it is the tree metric of the quartet weights. -/
theorem nanuqDistance_treeClass {T : Finset (Finset X)} (hT : IsUnrootedTree T) {x y : X} (hxy : x ≠ y) :
    nanuqDistance (treeClass T) x y = treeMetric T (External.Rhodes2020.quartetWeight T) x y := by
  rw [External.Rhodes2020.theorem2 hT hxy]
  refine nanuqDistance_eq_quartetDistance_of_rho fun q _ _ _ => ?_
  by_cases h : ∃ s ∈ treesOn q, Displays T s
  · have hspec := h.choose_spec
    have hq' : ¬ q ∈ {q : Finset X | ∀ s ∈ treesOn q, ¬ Displays T s} := fun hn =>
      hn _ hspec.1 hspec.2
    have hiff : (∃ s ∈ {s : QuartetTree X | Displays T s}, s.taxa = q ∧ Separated s x y) ↔
        Separated h.choose x y := by
      constructor
      · rintro ⟨s, hs, hst, hsep⟩
        have : s = h.choose := IsUnrootedTree.displays_unique hT hs hspec.2
          (hst.trans (mem_treesOn.1 hspec.1).symm)
        rwa [← this]
      · exact fun hsep => ⟨h.choose, hspec.2, mem_treesOn.1 hspec.1, hsep⟩
    simp only [treeClass, dite_eq_left h, rho, hq', false_or, hiff]
  · have hq' : q ∈ {q : Finset X | ∀ s ∈ treesOn q, ¬ Displays T s} := fun s hs hd => h ⟨s, hs, hd⟩
    have hc : treeClass T q = .star := dite_eq_right h
    rw [hc, ite_eq_left (Or.inl hq')]
    rfl

/-! ### Star trees and the sum of the distances -/

/-- The total of `ρ` over the ordered pairs of a set of four taxa. -/
private def pairTotal (C : QuartetClass X) (q : Finset X) : ℝ := ∑ x ∈ q, ∑ y ∈ q.erase x, rho C x y

omit [Fintype X] in
/-- On a quartet tree, four ordered pairs are in a cherry, and eight are separated. -/
private theorem sum_sum_ite_separated (s : QuartetTree X) (A B : ℝ) :
    ∑ x ∈ s.taxa, ∑ y ∈ s.taxa.erase x, (if Separated s x y then A else B) = 8 * A + 4 * B := by
  obtain ⟨a, b, c, d, h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hsep : ∀ x y : X, Separated (quartetTree a b c d h) x y ↔
      (x = a ∨ x = b ∨ x = c ∨ x = d) ∧ (y = a ∨ y = b ∨ y = c ∨ y = d) ∧
        ¬ ((x = a ∨ x = b) ∧ (y = a ∨ y = b)) ∧ ¬ ((x = c ∨ x = d) ∧ (y = c ∨ y = d)) := by
    intro x y
    simp only [Separated, quartetTree_taxa, quartetTree_val, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  have he₁ : ({a, b, c, d} : Finset X).erase a = {b, c, d} := by
    ext t; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind
  have he₂ : ({a, b, c, d} : Finset X).erase b = {a, c, d} := by
    ext t; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind
  have he₃ : ({a, b, c, d} : Finset X).erase c = {a, b, d} := by
    ext t; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind
  have he₄ : ({a, b, c, d} : Finset X).erase d = {a, b, c} := by
    ext t; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind
  rw [quartetTree_taxa]
  rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd, he₁, he₂, he₃, he₄]
  rw [Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_pair hcd,
    Finset.sum_insert (by simp [hac, had]), Finset.sum_pair hcd,
    Finset.sum_insert (by simp [hab, had]), Finset.sum_pair hbd,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  simp only [hsep]
  simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  ring

omit [Fintype X] in
private theorem pairTotal_star {q : Finset X} (hq : q.card = 4) : pairTotal (.star : QuartetClass X) q = 12 := by
  have hin : ∀ x ∈ q, ∑ y ∈ q.erase x, rho (.star : QuartetClass X) x y = 3 := by
    intro x hx
    simp [rho, Finset.card_erase_of_mem hx, hq]
  rw [pairTotal, Finset.sum_congr rfl hin]
  simp [hq]
  norm_num

/-- A tree and a 4-cycle have the same total, `8`, and a star tree has `12`. -/
private theorem pairTotal_of_isClassOn {C : QuartetClass X} {q : Finset X} (hq : q.card = 4) (h : IsClassOn C q) :
    (C = .star ∧ pairTotal C q = 12) ∨ (C ≠ .star ∧ pairTotal C q = 8) := by
  rcases C with _ | s | s
  · exact Or.inl ⟨rfl, pairTotal_star hq⟩
  · refine Or.inr ⟨by simp, ?_⟩
    have hst : s.taxa = q := mem_treesOn.1 h
    subst hst
    have := sum_sum_ite_separated s 1 0
    simp only [pairTotal, rho]
    rw [this]
    norm_num
  · refine Or.inr ⟨by simp, ?_⟩
    have hst : s.taxa = q := mem_treesOn.1 h
    subst hst
    have := sum_sum_ite_separated s (1 / 2) 1
    simp only [pairTotal, rho]
    rw [this]
    norm_num

/-- The triple sum of `ρ` over ordered pairs and the sets containing them, by the sets first. -/
private theorem sum_sum_sum_rho (cl : Finset X → QuartetClass X) :
    ∑ x, ∑ y ∈ univ.erase x, ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q), rho (cl q) x y =
      ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4), pairTotal (cl q) q := by
  have hL : ∀ x : X, ∑ y ∈ univ.erase x, ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4 ∧ x ∈ q ∧ y ∈ q),
      rho (cl q) x y = ∑ y, ∑ q : Finset X,
        if q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ y ≠ x then rho (cl q) x y else 0 := by
    intro x
    rw [← Finset.sum_erase univ (a := x) (f := fun y => ∑ q : Finset X,
      if q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ y ≠ x then rho (cl q) x y else 0)
      (Finset.sum_eq_zero fun q _ => by simp)]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [hyx]
  have hR : ∀ q ∈ univ.filter (fun q : Finset X => q.card = 4), pairTotal (cl q) q =
      ∑ x, ∑ y, if q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ y ≠ x then rho (cl q) x y else 0 := by
    intro q hq
    have hq4 : q.card = 4 := (mem_filter.1 hq).2
    rw [pairTotal, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ q)]
    rw [Finset.sum_eq_zero (s := univ.filter fun x => ¬ x ∈ q)
      (fun x hx => Finset.sum_eq_zero fun y _ => by simp [(mem_filter.1 hx).2]), add_zero]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ q.erase x)]
    rw [Finset.sum_eq_zero (s := univ.filter fun y => ¬ y ∈ q.erase x) (fun y hy => ?_), add_zero]
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨hyx, hyq⟩ := Finset.mem_erase.1 hy
      simp [hq4, hx, hyq, hyx]
    · have := (mem_filter.1 hy).2
      rw [Finset.mem_erase] at this
      rw [ite_eq_right]
      rintro ⟨-, -, h₁, h₂⟩
      exact absurd ⟨h₂, h₁⟩ this
  rw [Finset.sum_congr rfl hR, Finset.sum_congr rfl fun x _ => hL x]
  calc ∑ x : X, ∑ y : X, ∑ q : Finset X, (if q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ y ≠ x then rho (cl q) x y else 0)
      = ∑ x : X, ∑ q : Finset X, ∑ y : X, (if q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ y ≠ x then rho (cl q) x y else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ q : Finset X, ∑ x : X, ∑ y : X, (if q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ y ≠ x then rho (cl q) x y else 0) :=
        Finset.sum_comm
    _ = _ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun q _ hq => ?_).symm
        have hq4 : q.card ≠ 4 := fun h => hq (mem_filter.2 ⟨mem_univ _, h⟩)
        exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by simp [hq4]

/-- A classification with a star tree on some set of four taxa has a larger sum of distances than one with none, since
a tree and a 4-cycle have the same total of `ρ`, and a star tree a larger one. So the distances differ. -/
theorem nanuqDistance_ne_of_star {cl cl' : Finset X → QuartetClass X}
    (hcl : ∀ q : Finset X, q.card = 4 → IsClassOn (cl q) q)
    (hcl' : ∀ q : Finset X, q.card = 4 → IsClassOn (cl' q) q ∧ cl' q ≠ .star) {q₀ : Finset X}
    (hq₀ : q₀.card = 4) (h : cl q₀ = .star) : nanuqDistance cl ≠ nanuqDistance cl' := by
  intro heq
  have hsum : ∀ c : Finset X → QuartetClass X, ∑ x, ∑ y ∈ univ.erase x, nanuqDistance c x y =
      2 * (∑ q ∈ univ.filter (fun q : Finset X => q.card = 4), pairTotal (c q) q) +
        ∑ x : X, ∑ _y ∈ univ.erase x, (2 * (Fintype.card X : ℝ) - 4) := by
    intro c
    rw [← sum_sum_sum_rho, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [nanuqDistance, ite_eq_right (Finset.mem_erase.1 hy).1.symm]
    ring
  have h₁ := hsum cl
  rw [heq, hsum cl'] at h₁
  have hlt : ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4), pairTotal (cl' q) q <
      ∑ q ∈ univ.filter (fun q : Finset X => q.card = 4), pairTotal (cl q) q := by
    refine Finset.sum_lt_sum (fun q hq => ?_) ⟨q₀, mem_filter.2 ⟨mem_univ _, hq₀⟩, ?_⟩
    · have hq4 : q.card = 4 := (mem_filter.1 hq).2
      obtain ⟨hc', hns⟩ := hcl' q hq4
      have h₂ : pairTotal (cl' q) q = 8 := by
        rcases pairTotal_of_isClassOn hq4 hc' with h' | h'
        · exact absurd h'.1 hns
        · exact h'.2
      rw [h₂]
      rcases pairTotal_of_isClassOn hq4 (hcl q hq4) with h' | h'
      · rw [h'.2]
        norm_num
      · exact h'.2.ge
    · obtain ⟨hc', hns⟩ := hcl' q₀ hq₀
      have h₂ : pairTotal (cl' q₀) q₀ = 8 := by
        rcases pairTotal_of_isClassOn hq₀ hc' with h' | h'
        · exact absurd h'.1 hns
        · exact h'.2
      rw [h₂, h, pairTotal_star hq₀]
      norm_num
  linarith

/-! ### Two errors in the proof of Theorem 36 -/

section Errors

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ} {sides : Γ → Finset (Finset X)}

private lemma log_chiSqOneTail_ge {t : ℝ} (ht : 0 ≤ t) :
    -Real.log (√(2 * Real.pi)) - 1 - t ≤ Real.log (chiSqOneTail t) := by
  have h1 := QuartetTests.gaussianPDFReal_le_chiSqOneTail t
  have h2 := Real.log_le_log (ProbabilityTheory.gaussianPDFReal_pos _ _ _ one_ne_zero) h1
  refine le_trans ?_ h2
  have hpi : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.log_mul (inv_ne_zero hpi.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  have h3 : √t ^ 2 = t := Real.sq_sqrt ht
  nlinarith [sq_nonneg (√t - 1)]

/-- Levels of a smaller exponential order than the statistic do not reject. If the limit `d₁` of the statistic on `q₁`
has `40 d₁ < D`, then at levels below `P(χ²₂ > m D/2)` the p-value on `q₁` is not below the level, with probability
tending to one. -/
theorem not_rejects_below (hd : IsDist dist) {q₁ : Finset X} (hq₁ : q₁.card = 4) {D : ℝ}
    (hD : 40 * t3Stat (displayCF dist sides) q₁ < D) {α : ℕ → ℝ}
    (hα : ∀ m : ℕ, α m ≤ chiSqTwoTail (m * (D / 2))) :
    Tendsto (fun m : ℕ => iidProb dist m fun ω =>
      ∀ u ∈ treesOn q₁, α m ≤ t3PValue (quartetCount sides ω) u) atTop (𝓝 1) := by
  set d₁ := t3Stat (displayCF dist sides) q₁ with hd₁
  set ε := (D - 40 * d₁) / 80 with hε
  have hε₀ : 0 < ε := by rw [hε]; linarith
  set e := d₁ + ε with he
  have hgap : 10 * e < D / 4 := by rw [he, hε]; linarith
  have hd₁nn : 0 ≤ d₁ := QuartetTests.t3Stat_nonneg (QuartetTests.displayCF_nonneg hd) hq₁
  have he₀ : 0 < e := by rw [he]; linarith
  set C := -Real.log (√(2 * Real.pi)) - 1 - Real.log 2 with hC
  have hgap' : 0 < D / 4 - 10 * e := by linarith
  have hlarge : ∀ᶠ m : ℕ in atTop, -C < (m : ℝ) * (D / 4 - 10 * e) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hgap').eventually_gt_atTop (-C)
  refine tendsto_iidProb_of_imp hd ?_ (tendsto_t3Stat_near (sides := sides) hd hq₁ hε₀)
  filter_upwards [hlarge, eventually_gt_atTop 0] with m hm hm0 ω hω u hu
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hc := QuartetTests.quartetCount_nonneg (sides := sides) ω
  have hlow := QuartetTests.half_chiSqOneTail_le_t3PValue hc u
  rw [mem_treesOn.1 hu] at hlow
  have hstat := hω.2
  have hstat0 : 0 ≤ t3Stat (quartetCount sides ω) q₁ := QuartetTests.t3Stat_nonneg hc hq₁
  have hmono : chiSqOneTail (10 * (m * e)) < chiSqOneTail (10 * t3Stat (quartetCount sides ω) q₁) :=
    QuartetTests.chiSqOneTail_lt_of_lt (by positivity) (by linarith)
  have hval : chiSqTwoTail (m * (D / 2)) ≤ 1 / 2 * chiSqOneTail (10 * (m * e)) := by
    have hpos : 0 < 1 / 2 * chiSqOneTail (10 * (m * e)) := by
      have := QuartetTests.chiSqOneTail_pos (10 * ((m : ℝ) * e))
      positivity
    rw [chiSqTwoTail, ← Real.le_log_iff_exp_le hpos, Real.log_mul (by norm_num)
      (QuartetTests.chiSqOneTail_pos _).ne', one_div, Real.log_inv]
    have h₁ := log_chiSqOneTail_ge (t := 10 * ((m : ℝ) * e)) (by positivity)
    nlinarith
  exact (hα m).trans (hval.trans (by linarith))

/-- **The minimum in the proof of Theorem 36 does not reject.** The source: "we choose `α_m` to be the minimum of the
`α'_m` for these subsets, to ensure the probability of rejecting the null hypothesis for all of them goes to 1" (lines
2207-2209), where `α'_m = P(W_m > m d/2)` (lines 2195-2196). Take two sets of four taxa, `q₁` off the null, with
limits of the statistic `d₁`, `d₂` where `40 d₁ < d₂`. For any parameters `φ₁, φ₂` of the law `W_m`, the p-value on
`q₁` is not below the minimum of the two levels, with probability tending to one: the test does not reject on `q₁`. A
rejection needs a level above `α'_m`, so that the right choice is the maximum (`exists_levels`). The factor `40` is
only what the uniform lower bound for the tail gives. -/
theorem not_rejects_at_minimum (hd : IsDist dist) {q₁ q₂ : Finset X} (hq₁ : q₁.card = 4) (hq₂ : q₂.card = 4)
    (h40 : 40 * t3Stat (displayCF dist sides) q₁ < t3Stat (displayCF dist sides) q₂)
    (φ₁ : ℝ) {φ₂ : ℝ} (hφ₂ : φ₂ ≤ 1) :
    Tendsto (fun m : ℕ => iidProb dist m fun ω => ∀ u ∈ treesOn q₁,
      min (t3Tail φ₁ m (m * (t3Stat (displayCF dist sides) q₁ / 2)))
        (t3Tail φ₂ m (m * (t3Stat (displayCF dist sides) q₂ / 2))) ≤ t3PValue (quartetCount sides ω) u)
      atTop (𝓝 1) := by
  have hd₂ : 0 ≤ t3Stat (displayCF dist sides) q₂ :=
    QuartetTests.t3Stat_nonneg (QuartetTests.displayCF_nonneg hd) hq₂
  refine not_rejects_below hd hq₁ h40 fun m => (min_le_right _ _).trans ?_
  refine QuartetTests.t3Tail_le_chiSqTwoTail ?_ (by positivity)
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 hφ₂)) (Real.sqrt_nonneg _)

/-- The concordance factors of Figure 5 (L), as printed in the source for the quartet network with a `3₂`-cycle (lines
572-596, read in the published version): `CF_AB|CD`, with `x_i = e^{-t_i}`. -/
def figure5CFab (γ x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  (1 - γ) ^ 2 * (1 - 2 / 3 * x₁ * x₂) + 2 * γ * (1 - γ) * (1 - x₁ + 1 / 3 * x₁ * x₃) + γ ^ 2 * (1 - 2 / 3 * x₁ * x₄)

/-- `CF_AC|BD = CF_AD|BC` of Figure 5 (L), as printed. -/
def figure5CFac (γ x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  (1 - γ) ^ 2 * (1 / 3 * x₁ * x₂) + γ * (1 - γ) * x₁ * (1 - 1 / 3 * x₃) + γ ^ 2 * (1 / 3 * x₁ * x₄)

/-- **A `3₂`-cycle at the centroid**, by the source's own formula: at `γ = 1/2`, `x₁ = 40/43`, `x₂ = x₄ = 9/10`, `x₃ =
1/2`, all branch lengths positive, the printed concordance factor is `(1/3, 1/3, 1/3)`. Its two smallest entries are
equal, so it is tree-like in the sense of Definition 8, which says so of this point. The proof of Theorem 36 says
"Since the network is binary, the true multinomial parameter values are `CF = (p₁, p₂, p₃)` with `p_i ≠ 1/3` or `0`"
(line 2023), and that is false here. The point is on the boundary `CF_AB|CD = CF_AC|BD` of the tree-like region of
equation (1). The formula is derived from the definition of the NMSC, for a rooted form of that network, in
`src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean` (`ThreeTwo.nmscCF_N₃_abcd`, `ThreeTwo.centroid_N₃`). -/
theorem figure5_centroid :
    figure5CFab (1 / 2) (40 / 43) (9 / 10) (1 / 2) (9 / 10) = 1 / 3 ∧
      figure5CFac (1 / 2) (40 / 43) (9 / 10) (1 / 2) (9 / 10) = 1 / 3 := by
  norm_num [figure5CFab, figure5CFac]

/-- Equation (1) of the source, for the printed formula. -/
theorem figure5_equation_one (γ x₁ x₂ x₃ x₄ : ℝ) :
    figure5CFab γ x₁ x₂ x₃ x₄ - figure5CFac γ x₁ x₂ x₃ x₄ =
      1 - x₁ * ((1 - γ) ^ 2 * x₂ + γ * (1 - γ) * (3 - x₃) + γ ^ 2 * x₄) := by
  unfold figure5CFab figure5CFac
  ring

/-- The source's sufficient condition stays off the centroid: "provided `x₁ ≤ 4/5` (that is, `t₁ ≥ log(5/4)`), then a
tree-like CF results regardless of all other parameter values" (lines 637-639), and Proposition 10 uses it. With `t₃ <
∞`, as a metric network has, the inequality of the printed formula is strict. So the source's note after the proof of
Theorem 36, that its hypothesis "can be ensured through" Proposition 10, gives the corrected hypothesis too. -/
theorem figure5_lt {γ x₁ x₂ x₃ x₄ : ℝ} (hx₁₀ : 0 ≤ x₁) (hx₁ : x₁ ≤ 4 / 5) (hx₂ : x₂ ≤ 1)
    (hx₃₀ : 0 < x₃) (hx₃ : x₃ ≤ 1) (hx₄ : x₄ ≤ 1) :
    figure5CFac γ x₁ x₂ x₃ x₄ < figure5CFab γ x₁ x₂ x₃ x₄ := by
  have hB : (1 - γ) ^ 2 * x₂ + γ * (1 - γ) * (3 - x₃) + γ ^ 2 * x₄ ≤ (5 - x₃) / 4 := by
    have h₂ : (1 - γ) ^ 2 * x₂ ≤ (1 - γ) ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hx₂
    have h₄ : γ ^ 2 * x₄ ≤ γ ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hx₄
    have hg : γ * (1 - γ) ≤ 1 / 4 := by nlinarith [sq_nonneg (γ - 1 / 2)]
    have hg' : γ * (1 - γ) * (1 - x₃) ≤ 1 / 4 * (1 - x₃) :=
      mul_le_mul_of_nonneg_right hg (by linarith)
    nlinarith
  have hx : x₁ * ((1 - γ) ^ 2 * x₂ + γ * (1 - γ) * (3 - x₃) + γ ^ 2 * x₄) ≤ 4 / 5 * ((5 - x₃) / 4) :=
    (mul_le_mul_of_nonneg_left hB hx₁₀).trans (mul_le_mul_of_nonneg_right hx₁ (by linarith))
  have := figure5_equation_one γ x₁ x₂ x₃ x₄
  linarith

/-- At the centroid, for a fixed level `β`, the star test rejects with probability tending to `β`. -/
theorem tendsto_star_le_of_centroid (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides) {q : Finset X}
    (hq : q.card = 4) (h : ∀ r ∈ treesOn q, displayCF dist sides r = 1 / 3) {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    Tendsto (fun n => iidProb dist n fun ω => starPValue .lrt (quartetCount sides ω) q ≤ β) atTop (𝓝 β) :=
  QuartetTests.starPValue_asymptoticallyUniform .lrt hd hs hq h β h0 h1

/-- **At a concordance factor at the centroid, with a fixed level `β < 1`, the distance does not converge to one
without star trees.** With probability tending to `1 - β` the star test does not reject there, and NANUQ gives "star
tree" priority (line 1916), so that the computed distance is not that of a classification with no star tree
(`nanuqDistance_ne_of_star`). This is for any levels `α`. So the first sentence of the proof of Theorem 36 fails at
such a point. -/
theorem not_tendsto_of_centroid (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides)
    {cl' : Finset X → QuartetClass X} (hcl' : ∀ q : Finset X, q.card = 4 → IsClassOn (cl' q) q ∧ cl' q ≠ .star)
    {q₀ : Finset X} (hq₀ : q₀.card = 4) (h : ∀ r ∈ treesOn q₀, displayCF dist sides r = 1 / 3)
    {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (α : ℕ → ℝ)
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) :
    ¬ Tendsto (fun n => iidProb dist n fun ω =>
      nanuqDistance (classify mlT mlC (α n) β (quartetCount sides ω)) = nanuqDistance cl') atTop (𝓝 1) := by
  intro hlim
  have hle : ∀ n, iidProb dist n (fun ω =>
      nanuqDistance (classify mlT mlC (α n) β (quartetCount sides ω)) = nanuqDistance cl') ≤
      iidProb dist n fun ω => starPValue .lrt (quartetCount sides ω) q₀ ≤ β := by
    intro n
    refine iidProb_mono hd fun ω hω => ?_
    by_contra hnot
    refine nanuqDistance_ne_of_star (cl := classify mlT mlC (α n) β (quartetCount sides ω)) (cl' := cl')
      (fun q hq => classify_isClassOn hmlT hmlC _ _ _ hq) hcl' hq₀ ?_ hω
    rw [classify, ite_eq_left (not_le.1 hnot).le]
  exact absurd (le_of_tendsto_of_tendsto' hlim (tendsto_star_le_of_centroid hd hs hq₀ h h0 h1.le) hle)
    (not_le.2 h1)

/-- **At levels `β_n → 0`, at the centroid, the distance is not one without star trees**, with probability tending to
one: the star test does not reject there, and so on that set Step 2 says "star tree". So levels `β_n → 0` make the
answer at the centroid deterministic, which a fixed `β` does not, and it is the population value
(`tendsto_classify_eq_cfClass`). It is not the class of a `3₂`-cycle on the network. -/
theorem tendsto_ne_of_centroid (hd : IsDist dist) (hs : QuartetTests.DisplaysOne dist sides)
    {cl' : Finset X → QuartetClass X} (hcl' : ∀ q : Finset X, q.card = 4 → IsClassOn (cl' q) q ∧ cl' q ≠ .star)
    {q₀ : Finset X} (hq₀ : q₀.card = 4) (h : ∀ r ∈ treesOn q₀, displayCF dist sides r = 1 / 3)
    (α : ℕ → ℝ) {β : ℕ → ℝ} (hβ₀ : Tendsto β atTop (𝓝 0))
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb dist n fun ω =>
      nanuqDistance (classify mlT mlC (α n) (β n) (quartetCount sides ω)) ≠ nanuqDistance cl') atTop (𝓝 1) := by
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_) (tendsto_le_starPValue hd hs hq₀ h hβ₀)
  refine nanuqDistance_ne_of_star (fun q hq => classify_isClassOn hmlT hmlC _ _ _ hq) hcl' hq₀ ?_
  rw [classify, ite_eq_left hω]

end Errors

/-! ### The network -/

section Network

variable {V E : Type*}

/-- The quartet tree `s` is displayed by a tree of the grove `G(N⁻)` (Definition 13): with one parent kept at every
vertex, the arcs kept form a spanning tree of the network, and an arc of it induces the split of `s`
(`RootedNetwork.SplitOffAt`). -/
def GroveDisplays (N : RootedNetwork V E X) (s : QuartetTree X) : Prop :=
  ∃ D : Set E, N.IsDeletion D ∧ (∀ f g, f ∉ D → g ∉ D → N.graph.target f = N.graph.target g → f = g) ∧
    ∃ e, N.SplitOffAt D e s

/-- The network's induced 4-taxon network on `q` has a `3₂`-cycle: a reticulation with exactly two taxa of `q` below
it, the other two being in different blocks at its blob (TOB-QMC's blocks, `TOBQMC.Level1.BlockWalk`), so that the
three parts of `q` meet the cycle at three vertices.

The source's definition is by the cycles of the unrooted induced network `N⁻`, which is not formalized. That the two
agree is not proved; `Proposition9.lean` says what is. -/
def HasThreeTwoCycle (N : RootedNetwork V E X) (q : Finset X) : Prop :=
  ∃ h : V, 2 ≤ N.graph.indegree h ∧ (q.filter fun x => N.graph.Reaches h (N.leaf x)).card = 2 ∧
    ∀ x ∈ q, ∀ y ∈ q, x ≠ y → ¬ N.graph.Reaches h (N.leaf x) → ¬ N.graph.Reaches h (N.leaf y) →
      ¬ TOBQMC.Level1.BlockWalk N h (N.leaf x) (N.leaf y)

/-- The hypothesis of Theorem 36 (line 2003), as printed: "all induced quartet networks with `3₂`-cycles are
tree-like", tree-like being Definition 8 (line 409), "the two smallest entries of the concordance factor are equal":
`IsT3Null`. This includes the centroid: "If `CF = (1/3, 1/3, 1/3)`, then it supports all three quartets". -/
def ThreeTwoTreelike (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop :=
  ∀ q : Finset X, q.card = 4 → HasThreeTwoCycle N q → IsT3Null p q

/-- **What Theorem 36 uses of the source's Proposition 9**, on concordance factors of level-1 networks. The source
takes it from its references [1, 3]. It is proved on binary level-1 networks in `Proposition9.lean` (`proposition9`).
The parts:

* `no_three_two`: part 1. If `Q` has no `4₁`-cycle or `3₂`-cycle, its concordance factor supports `Q̃`, for a split
  that the tree of blobs displays; for one it does not display, this is proved,
  `TOBQMC.Level1.nmscCF_lt_of_not_displays`, and the equality of the alternatives is proved for all networks,
  `NMSC.cut_alternatives`;
* `cycle_exists`, `cycle_min`: part 3. A set of four taxa with no cut-edge split on its induced network has a 4-cycle,
  with circular order `a, b, c, d` say. The grove displays `ab|cd` and `ad|bc`, not `ac|bd` (Figure 6), and `CF_AB|CD
  > CF_AC|BD`, `CF_AD|BC > CF_AC|BD`. Its topological half, `cycle_exists`, is the classification of level-1 quartet
  networks that the source uses before Proposition 9 ("exactly 6 types of cycles", line 401); it is what makes
  `networkClass` the `Q̃` of Definition 20.

Part 2 (the extended line segment) is not needed: its equality is `NMSC.cut_alternatives`. -/
structure Proposition9 (N : RootedNetwork V E X) (p : QuartetTree X → ℝ) : Prop where
  no_three_two : ∀ s : QuartetTree X, Displays (treeOfBlobs N) s → ¬ HasThreeTwoCycle N s.taxa →
    ∀ r ∈ s.alternatives, p r < p s
  cycle_exists : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
    ∃ s ∈ treesOn q, ¬ GroveDisplays N s ∧ ∃ r ∈ s.alternatives, GroveDisplays N r
  cycle_min : ∀ s : QuartetTree X, ¬ IsTreelike N s.taxa → ¬ GroveDisplays N s → IsStrictMin p s

/-- **The class of a set of four taxa on the network**, the `Q̃_xyzw` of Definition 20: the quartet tree when the
induced network has a cut-edge split on it, which is the case after contracting its 2- and 3-cycles; otherwise the
4-cycle, given by a quartet tree that its grove does not display, with an alternative that it does, whose cherries are
the taxa opposite on the cycle; and otherwise, when the grove displays no quartet tree on the set, the star tree of
the source's extension (lines 1964-1968). In a binary level-1 network there is no star tree, by
`Proposition9.cycle_exists`.

The source's `Q̃` is by the contraction `N_c⁻`, which is not formalized. That the two agree is not proved;
`Proposition9.lean` says what is (`networkClass_eq_tree`, `networkClass_eq_cycle`, `not_isTreelike_iff`). -/
def networkClass (N : RootedNetwork V E X) (q : Finset X) : QuartetClass X :=
  if h : ∃ s ∈ treesOn q, InducedCutSplit N s then .tree h.choose
  else if h' : ∃ s ∈ treesOn q, ¬ GroveDisplays N s ∧ ∃ r ∈ s.alternatives, GroveDisplays N r then .cycle h'.choose
  else .star

theorem networkClass_isClassOn (N : RootedNetwork V E X) (q : Finset X) : IsClassOn (networkClass N q) q := by
  unfold networkClass
  split_ifs with h h'
  · exact h.choose_spec.1
  · exact h'.choose_spec.1
  · trivial

/-- With a 4-cycle wherever there is no cut-edge split, the network's classification has no star tree. -/
theorem networkClass_ne_star {N : RootedNetwork V E X}
    (h : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      ∃ s ∈ treesOn q, ¬ GroveDisplays N s ∧ ∃ r ∈ s.alternatives, GroveDisplays N r) {q : Finset X}
    (hq : q.card = 4) : networkClass N q ≠ .star := by
  unfold networkClass
  split_ifs with h₁ h₂
  · simp
  · simp
  · exact absurd (h q hq h₁) h₂

/-- The theoretical quartet distance `d_{Q,N⁻}` of Definition 22. -/
def networkDistance (N : RootedNetwork V E X) : X → X → ℝ := nanuqDistance (networkClass N)

variable [Fintype V] [Fintype E]

/-- Gene trees under the NMSC are binary. As in `src/TINNiK/T3.lean`, where it is private. -/
theorem displaysOne_nmsc [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E} {ρ : ℝ} :
    QuartetTests.DisplaysOne (geneTreeDist N θ ρ) (unroot (L := X)) := by
  intro g hg q hq
  obtain ⟨hH, hbin⟩ := isBinaryHierarchy_iff_card_childClusters.1 (geneTreeDist_support hN hg)
  have hbt : IsBinaryTree (unroot g) := ⟨g, hH, rfl, hbin⟩
  obtain ⟨s, hs, hd⟩ := hbt.exists_displays hq
  refine ⟨s, ⟨hs, hd⟩, fun s' h' => ?_⟩
  exact IsUnrootedTree.displays_unique ⟨g, hH, rfl⟩ h'.2 hd
    (by rw [(Finset.mem_filter.mp h'.1).2, (Finset.mem_filter.mp hs).2])

theorem isDist_geneTreeDist [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : IsDist (geneTreeDist N θ ρ) :=
  ⟨geneTreeDist_nonneg hN hθ hρ, sum_geneTreeDist hN hθ hρ⟩

/-- **On a cut-edge split, the concordance factor is strictly on its half-line**, under the hypothesis of Theorem 36
and Proposition 9, off the centroid. A split the tree of blobs does not display needs neither:
`TOBQMC.Level1.nmscCF_lt_of_not_displays`. -/
theorem isT1Strict_of_inducedCutSplit [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hP9 : Proposition9 N (nmscCF N θ ρ)) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) {s : QuartetTree X} (hs : InducedCutSplit N s) :
    IsT1Strict (nmscCF N θ ρ) s := by
  have halt := NMSC.cut_alternatives hN hθ hρ s hs
  refine ⟨fun r hr => ?_, halt⟩
  by_cases hd : Displays (treeOfBlobs N) s
  · by_cases h3 : HasThreeTwoCycle N s.taxa
    · have hq := s.card_taxa
      have hsum : ∑ r ∈ treesOn s.taxa, nmscCF N θ ρ r = 1 :=
        QuartetTests.sum_displayCF_treesOn (isDist_geneTreeDist hN hθ hρ) (displaysOne_nmsc hN) hq
      rcases cf_trichotomy hq hsum with huni | ⟨s', hs', hstrict⟩ | ⟨hnull, -⟩
      · exact absurd huni (hcen _ hq)
      · have hst : s'.taxa = s.taxa := mem_treesOn.1 hs'
        by_cases hss : s' = s
        · rw [← hss] at hr ⊢
          exact hstrict.1 r hr
        · exfalso
          have h₁ : s' ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨hst, hss⟩
          obtain ⟨r₁, r₂, hne, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s
          have hmem₁ : r₁ ∈ s.alternatives := by rw [ha]; simp
          have hmem₂ : r₂ ∈ s.alternatives := by rw [ha]; simp
          -- the other alternative of `s` is an alternative of `s'`, with the same value
          have key : ∀ u ∈ s.alternatives, u ≠ s' → False := fun u hu hne' =>
            (hstrict.1 u (QuartetTree.mem_alternatives.2
              ⟨(QuartetTree.mem_alternatives.1 hu).1.trans hst.symm, hne'⟩)).ne (halt u hu s' h₁)
          by_cases h' : r₁ = s'
          · exact key r₂ hmem₂ fun he => hne (h'.trans he.symm)
          · exact key r₁ hmem₁ h'
      · exact absurd (h32 _ hq h3) hnull
    · exact hP9.no_three_two s hd h3 r hr
  · exact TOBQMC.Level1.nmscCF_lt_of_not_displays hN hLevel hθ hρ hs hd hr

/-- The hypotheses give what the T3 test needs, in `src/TINNiK/T3.lean`. So they also give the T3 option of TINNiK. -/
theorem t3Detectable_of_proposition9 [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hP9 : Proposition9 N (nmscCF N θ ρ)) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) : TINNiK.T3Detectable N (nmscCF N θ ρ) := by
  refine ⟨fun s hs => isT1Strict_of_inducedCutSplit hN hLevel hθ hρ hP9 h32 hcen hs, fun q hq hnt hnull => ?_⟩
  obtain ⟨s, hs, hn, -⟩ := hP9.cycle_exists q hq hnt
  have hst : s.taxa = q := mem_treesOn.1 hs
  have hmin := hP9.cycle_min s (hst ▸ hnt) hn
  obtain ⟨s', hs', hle, heq⟩ := hnull
  have hst' : s'.taxa = s.taxa := (mem_treesOn.1 hs').trans hst.symm
  obtain ⟨r₁, r₂, hne, ha⟩ := QuartetTests.QuartetTree.exists_alternatives s'
  have hmem₁ : r₁ ∈ s'.alternatives := by rw [ha]; simp
  have hmem₂ : r₂ ∈ s'.alternatives := by rw [ha]; simp
  by_cases hss : s = s'
  · subst hss
    exact absurd (hle r₁ hmem₁) (not_le.2 (hmin r₁ hmem₁))
  · have hmemS : s ∈ s'.alternatives := QuartetTree.mem_alternatives.2 ⟨hst'.symm, hss⟩
    have key : ∀ u ∈ s'.alternatives, u ≠ s → False := fun u hu hne' =>
      (hmin u (QuartetTree.mem_alternatives.2
        ⟨(QuartetTree.mem_alternatives.1 hu).1.trans hst', hne'⟩)).ne (heq s hmemS u hu)
    by_cases h' : r₁ = s
    · exact key r₂ hmem₂ fun he => hne (h'.trans he.symm)
    · exact key r₁ hmem₁ h'

/-- **The population value of Step 2 is the network's class**, under the hypotheses. -/
theorem cfClass_eq_networkClass [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hP9 : Proposition9 N (nmscCF N θ ρ)) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) {q : Finset X} (hq : q.card = 4) :
    cfClass (nmscCF N θ ρ) q = networkClass N q := by
  unfold networkClass
  by_cases h : ∃ s ∈ treesOn q, InducedCutSplit N s
  · rw [dite_eq_left h]
    exact cfClass_eq_tree h.choose_spec.1
      (isT1Strict_of_inducedCutSplit hN hLevel hθ hρ hP9 h32 hcen h.choose_spec.2)
  · have hex := hP9.cycle_exists q hq h
    rw [dite_eq_right h, dite_eq_left hex]
    have hst : hex.choose.taxa = q := mem_treesOn.1 hex.choose_spec.1
    exact cfClass_eq_cycle hex.choose_spec.1 (hP9.cycle_min _ (by rw [hst]; exact h) hex.choose_spec.2.1)


/-! ### Theorem 36 -/

/-- The event of the proof of Theorem 36, "It is enough to show that the `α_m` can be chosen so that with probability
approaching 1 the quartet distance computed in the NANUQ algorithm exactly agrees with the theoretical quartet
distance" (line 2009), on the way there: Step 2 gives the network's class on all sets of four taxa, so that the
distance of Step 3 is the theoretical one. For a level sequence `β` with `log(1/β_n) = o(n)`, such as a constant. -/
theorem tendsto_classify_eq_networkClass [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hP9 : Proposition9 N (nmscCF N θ ρ)) (h32 : ThreeTwoTreelike N (nmscCF N θ ρ))
    (hcen : TINNiK.NoCentroidCF (nmscCF N θ ρ)) {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝 0))
    (hrej : RejectsOffNull (geneTreeDist N θ ρ) unroot α) (hβ : ∀ n, 0 < β n)
    (hβlog : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0))
    {mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X} (hmlT : IsMaxCountSelection mlT)
    (hmlC : IsMinCountSelection mlC) :
    Tendsto (fun n => iidProb (geneTreeDist N θ ρ) n fun ω =>
      (∀ q : Finset X, q.card = 4 → classify mlT mlC (α n) (β n) (quartetCount unroot ω) q = networkClass N q) ∧
        nanuqDistance (classify mlT mlC (α n) (β n) (quartetCount unroot ω)) = networkDistance N) atTop (𝓝 1) := by
  have hd := isDist_geneTreeDist hN hθ hρ
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun n ω hω => ?_)
    (tendsto_classify_eq_cfClass hd (displaysOne_nmsc hN) (fun r => nmscCF_pos hN hθ hρ r) hα₀ hrej hβ hβlog
      (Or.inl hcen) hmlT hmlC)
  have hall : ∀ q : Finset X, q.card = 4 →
      classify mlT mlC (α n) (β n) (quartetCount unroot ω) q = networkClass N q := fun q hq =>
    (hω q hq).trans (cfClass_eq_networkClass hN hLevel hθ hρ hP9 h32 hcen hq)
  exact ⟨hall, nanuqDistance_congr hall⟩

/-- **Theorem 36 for any network and parameters with what it uses of Proposition 9.** The label and the discussion are
at `theorem36`, in `Proposition9.lean`, which gives `hP9` on a binary level-1 network. The network being binary is
used only through Proposition 9, so it is not a hypothesis here. -/
theorem theorem36_of_proposition9 [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) (hP9 : Proposition9 N (nmscCF N θ 0))
    (h32 : ThreeTwoTreelike N (nmscCF N θ 0)) (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0)) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          (∀ q : Finset X, q.card = 4 → classify mlT mlC (α m) β (quartetCount unroot ω) q = networkClass N q) ∧
            nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω)) = networkDistance N)
          atTop (𝓝 1) := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨α, hα₀, hαpos, hαlt, hrej⟩ :=
    exists_levels (isDist_geneTreeDist hN hθ hρ) (displaysOne_nmsc (θ := θ) (ρ := 0) hN)
  refine ⟨α, hαpos, hαlt, hα₀, fun β hβ _ mlT mlC hmlT hmlC => ?_⟩
  exact tendsto_classify_eq_networkClass hN hLevel hθ hρ hP9 h32 hcen hα₀ hrej (β := fun _ => β)
    (fun _ => hβ) (tendsto_log_const_div β) hmlT hmlC

/-- `theorem36_output`, with what it uses of Proposition 9. -/
theorem theorem36_output_of_proposition9 [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hLevel : IsLevelOne N) {θ : MetricData E} (hθ : N.IsMetric θ) (hP9 : Proposition9 N (nmscCF N θ 0))
    (h32 : ThreeTwoTreelike N (nmscCF N θ 0)) (hcen : TINNiK.NoCentroidCF (nmscCF N θ 0)) :
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        ∀ {Y : Type*} (A : (X → X → ℝ) → Y) (y : Y), A (networkDistance N) = y →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          A (nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω))) = y) atTop (𝓝 1) := by
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨α, hαpos, hαlt, hα₀, h⟩ := theorem36_of_proposition9 hN hLevel hθ hP9 h32 hcen
  refine ⟨α, hαpos, hαlt, hα₀, fun β hβ hβ₁ mlT mlC hmlT hmlC Y A y hA => ?_⟩
  refine tendsto_iidProb_of_imp (isDist_geneTreeDist hN hθ hρ) (Eventually.of_forall fun m ω hω => ?_)
    (h β hβ hβ₁ mlT mlC hmlT hmlC)
  rw [hω.2, hA]

/-- `theorem36_generic`, with what it uses of Proposition 9. -/
theorem theorem36_generic_of_proposition9 [Nonempty X] {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    (hBin : N.IsBinary) (hLevel : IsLevelOne N) :
    ∃ A : Set (MetricData E), IsGenericNull N A ∧
      ∀ θ, N.IsMetric θ → θ ∉ A → Proposition9 N (nmscCF N θ 0) → ThreeTwoTreelike N (nmscCF N θ 0) →
      ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
        ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
          IsMaxCountSelection mlT → IsMinCountSelection mlC →
          Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
            nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω)) = networkDistance N)
            atTop (𝓝 1) := by
  refine ⟨_, TINNiK.isGenericNull_centroid hN hBin, fun θ hθ hA hP9 h32 => ?_⟩
  have hcen : TINNiK.NoCentroidCF (nmscCF N θ 0) := by
    by_contra hn
    exact hA ⟨hθ, hn⟩
  obtain ⟨α, hαpos, hαlt, hα₀, h⟩ := theorem36_of_proposition9 hN hLevel hθ hP9 h32 hcen
  refine ⟨α, hαpos, hαlt, hα₀, fun β hβ hβ₁ mlT mlC hmlT hmlC => ?_⟩
  exact tendsto_iidProb_of_imp (isDist_geneTreeDist hN hθ ⟨le_rfl, zero_le_one⟩)
    (Eventually.of_forall fun m ω hω => hω.2) (h β hβ hβ₁ mlT mlC hmlT hmlC)

/-- Selections exist, when there is a set of four taxa: a topology of largest count on each. -/
theorem exists_isMaxCountSelection {q₀ : Finset X} (hq₀ : q₀.card = 4) :
    ∃ ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X, IsMaxCountSelection ml := by
  obtain ⟨s₀, -⟩ : (treesOn q₀).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq₀]
    norm_num
  have hex : ∀ (c : QuartetTree X → ℝ) (q : Finset X), ∃ s : QuartetTree X,
      q.card = 4 → s ∈ treesOn q ∧ ∀ r ∈ treesOn q, c r ≤ c s := by
    intro c q
    by_cases hq : q.card = 4
    · have hne : (treesOn q).Nonempty := by
        rw [← Finset.card_pos, card_treesOn hq]
        norm_num
      obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ c hne
      exact ⟨s, fun _ => ⟨hs, hmax⟩⟩
    · exact ⟨s₀, fun h => absurd h hq⟩
  choose ml hml using hex
  exact ⟨ml, fun c q hq => hml c q hq⟩

/-- Selections exist, when there is a set of four taxa: a topology of least count on each. -/
theorem exists_isMinCountSelection {q₀ : Finset X} (hq₀ : q₀.card = 4) :
    ∃ ml : (QuartetTree X → ℝ) → Finset X → QuartetTree X, IsMinCountSelection ml := by
  obtain ⟨s₀, -⟩ : (treesOn q₀).Nonempty := by
    rw [← Finset.card_pos, card_treesOn hq₀]
    norm_num
  have hex : ∀ (c : QuartetTree X → ℝ) (q : Finset X), ∃ s : QuartetTree X,
      q.card = 4 → s ∈ treesOn q ∧ ∀ r ∈ treesOn q, c s ≤ c r := by
    intro c q
    by_cases hq : q.card = 4
    · have hne : (treesOn q).Nonempty := by
        rw [← Finset.card_pos, card_treesOn hq]
        norm_num
      obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image _ c hne
      exact ⟨s, fun _ => ⟨hs, hmin⟩⟩
    · exact ⟨s₀, fun h => absurd h hq⟩
  choose ml hml using hex
  exact ⟨ml, fun c q hq => hml c q hq⟩

/-- **Theorem 36 as printed**, with its conclusion at the distance, as in the first sentence of its proof. -/
def Theorem36AsPrinted (N : RootedNetwork V E X) : Prop :=
  ∀ θ, N.IsMetric θ → ThreeTwoTreelike N (nmscCF N θ 0) →
    ∃ α : ℕ → ℝ, (∀ m, 0 < α m) ∧ (∀ m, 1 ≤ m → α m < 1) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ mlT mlC : (QuartetTree X → ℝ) → Finset X → QuartetTree X,
        IsMaxCountSelection mlT → IsMinCountSelection mlC →
        Tendsto (fun m => iidProb (geneTreeDist N θ 0) m fun ω =>
          nanuqDistance (classify mlT mlC (α m) β (quartetCount unroot ω)) = networkDistance N) atTop (𝓝 1)

/-- **The correction of Theorem 36 is needed.** If at some parameters satisfying the printed hypothesis a concordance
factor is at the centroid, then the conclusion fails at the level of the distance: for every sequence `α_m` and every
`β < 1`, the probability that the distance agrees with the theoretical one does not tend to one. The centroid is
reached by the formula that the source prints for a `3₂`-cycle (`figure5_centroid`).
`ThreeTwo.not_theorem36AsPrinted_N₃`, in `src/External/AllmanBanosRhodes2019/ThreeTwoCycle.lean`, applies this to a
concrete binary level-1 network.

What the splits graph then does after NeighborNet is not determined by this. On four taxa, though, the computed
distance is then the metric of the star tree, with no split `ab|cd`. -/
theorem not_theorem36AsPrinted {N : RootedNetwork V E X} [Nonempty X] (hN : N.IsPhylogenetic)
    (hcyc : ∀ q : Finset X, q.card = 4 → ¬ IsTreelike N q →
      ∃ s ∈ treesOn q, ¬ GroveDisplays N s ∧ ∃ r ∈ s.alternatives, GroveDisplays N r)
    {θ : MetricData E} (hθ : N.IsMetric θ) (h32 : ThreeTwoTreelike N (nmscCF N θ 0))
    (hcen : ¬ TINNiK.NoCentroidCF (nmscCF N θ 0)) : ¬ Theorem36AsPrinted N := by
  intro h
  have hρ : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  unfold TINNiK.NoCentroidCF at hcen
  push Not at hcen
  obtain ⟨q₀, hq₀, huni⟩ := hcen
  obtain ⟨α, -, -, -, hlim⟩ := h θ hθ h32
  obtain ⟨mlT, hmlT⟩ := exists_isMaxCountSelection hq₀
  obtain ⟨mlC, hmlC⟩ := exists_isMinCountSelection hq₀
  exact not_tendsto_of_centroid (isDist_geneTreeDist hN hθ hρ) (displaysOne_nmsc hN)
    (fun q hq => ⟨networkClass_isClassOn N q, networkClass_ne_star hcyc hq⟩) hq₀ huni
    (β := 1 / 2) (by norm_num) (by norm_num) α hmlT hmlC
    (hlim (1 / 2) (by norm_num) (by norm_num) mlT mlC hmlT hmlC)

end Network

end External.AllmanBanosRhodes2019
