module

public import ECToBlob.DisplayedTree
public import ECToBlob.DisplayedTreeExample
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Phylogenetics.Tree.FourPoint

/-!
# ECToBlob §10: sums of pairs of distances

"For example, input data could come from a concatenated multiple sequence alignment, summarized by pairwise distances `D`
between taxa, instead of quartet CFs. Indeed, tree-like distances can be characterized by the 4-point condition, which involves
3 sum-of-pair values similar to the 3 concordance factors: `(SP_ab|cd, SP_ac|bd, SP_ad|bc)` where `SP_xy|zt = D(x,y) + D(z,t)`.
Under adequate conditions on the network and on the model, the analogue of Assumption 1 for distances is met [33], and the tree
of blobs is identifiable from average pairwise distances. The ECToBlob framework could be applied to this input data type, under
models for which a trivial 4-blob (star) corresponds to equal SP values, and a cut-edge split (T1) corresponds to
`SP_ab|cd < SP_ac|bd = SP_ad|bc`, and provided that an adequate test is designed for each." (the paper's text, lines 1424-1432.)

* **The analogue of Assumption 1**: `SPForward`, `SPConverse`. It holds in the forward direction for the average distance of the
  displayed tree model on every network (`spForward_averageDist`), which is the argument of Proposition 6.1 of [33] (Rhodes, Baños,
  Xu, Ané 2025): the sums of pairs are a mixture over displayed trees. `sumOfPairs_sub_eq` is its identity,
  `SP_ac|bd - SP_ab|cd = 2 W(ab|cd) - 2 W(ac|bd)` for the weight `W` of the edges with each pattern. The converse holds when each set
  of four taxa has a trivial 4-blob, a cut split, or two displayed quartets and not the third (`spConverse_of_cases`), which is
  item 2 of that Proposition; that binary outer-labeled planar networks are of this kind is its Lemma 5.1, not formalized here.
  `Instance.spConverse_averageDist` is an instance.
* **Identifiability**: `treeOfBlobs_eq_of_eq`.
* **A test**: `contrastP`, by Hoeffding's inequality (`iidProb_mean_ge_le`): for a sample of `n` loci with bounded distances, a
  finite-sample valid p-value (`iidProb_contrastP_lt_le`). Its p-values are `1` with positive probability under the null, so it is
  adequate for Bon and BBC only (`adequateTests_sumOfPairs`), as the displayed tree model is.
* **The framework on this data type**: `consistency_sumOfPairs`, and `consistency_averageDist` for the displayed tree model.

The paper does not design a test, and says "provided that". The test here is one that makes the statement true.
-/

@[expose] public noncomputable section

open Phylogenetics Phylogenetics.RootedNetwork Finset Filter Topology
open scoped Classical

namespace ECToBlob.SumOfPairs

open ECToBlob.Deterministic ECToBlob.Coarsening ECToBlob.Framework ECToBlob.DisplayedTree

/-! ### Hoeffding's inequality for independent draws -/

section Hoeffding

variable {Γ : Type*} [Fintype Γ] {dist : Γ → ℝ}

/-- The moment generating function of a bounded variable of mean zero: the argument of Hoeffding's lemma. -/
theorem sum_mul_exp_le (hd : IsDist dist) {Y : Γ → ℝ} {L : ℝ} (hL : 0 < L) (hY : ∀ g, |Y g| ≤ L)
    (h0 : ∑ g, dist g * Y g = 0) (t : ℝ) :
    ∑ g, dist g * Real.exp (t * Y g) ≤ Real.exp ((t * L) ^ 2 / 2) := by
  have hpoint : ∀ g, Real.exp (t * Y g) ≤
      (L + Y g) / (2 * L) * Real.exp (t * L) + (L - Y g) / (2 * L) * Real.exp (-(t * L)) := by
    intro g
    have ⟨h₁, h₂⟩ := abs_le.1 (hY g)
    have ha : 0 ≤ (L + Y g) / (2 * L) := div_nonneg (by linarith) (by linarith)
    have hb : 0 ≤ (L - Y g) / (2 * L) := div_nonneg (by linarith) (by linarith)
    have hab : (L + Y g) / (2 * L) + (L - Y g) / (2 * L) = 1 := by
      field_simp
      ring
    have := convexOn_exp.2 (Set.mem_univ (t * L)) (Set.mem_univ (-(t * L))) ha hb hab
    simp only [smul_eq_mul] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    field_simp
    ring
  calc ∑ g, dist g * Real.exp (t * Y g)
      ≤ ∑ g, dist g * ((L + Y g) / (2 * L) * Real.exp (t * L) +
          (L - Y g) / (2 * L) * Real.exp (-(t * L))) :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hpoint g) (hd.1 g)
    _ = Real.cosh (t * L) := by
        have hsplit : ∀ g, dist g * ((L + Y g) / (2 * L) * Real.exp (t * L) +
            (L - Y g) / (2 * L) * Real.exp (-(t * L))) =
            dist g * ((Real.exp (t * L) + Real.exp (-(t * L))) / 2) +
              (dist g * Y g) * ((Real.exp (t * L) - Real.exp (-(t * L))) / (2 * L)) := by
          intro g
          field_simp
          ring
        simp only [hsplit]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hd.2, h0, Real.cosh_eq]
        ring
    _ ≤ _ := Real.cosh_le_exp_half_sq _

/-- (`ext:hoeffding`) **Hoeffding's inequality** for the mean of `n` independent draws, with mean at most zero. -/
theorem iidProb_mean_ge_le (hd : IsDist dist) {c : Γ → ℝ} {l : ℝ} (hl : 0 < l) (hc : ∀ g, |c g| ≤ l)
    (hμ : ∑ g, dist g * c g ≤ 0) {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    iidProb dist n (fun ω => t ≤ (∑ i, c (ω i)) / n) ≤ Real.exp (-(n * t ^ 2 / (8 * l ^ 2))) := by
  set μ := ∑ g, dist g * c g with hμdef
  have hμabs : |μ| ≤ l := by
    calc |μ| ≤ ∑ g, |dist g * c g| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ g, dist g * |c g| := Finset.sum_congr rfl fun g _ => by rw [abs_mul, abs_of_nonneg (hd.1 g)]
      _ ≤ ∑ g, dist g * l := Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hc g) (hd.1 g)
      _ = l := by rw [← Finset.sum_mul, hd.2, one_mul]
  set Y : Γ → ℝ := fun g => c g - μ with hY
  have hY₀ : ∑ g, dist g * Y g = 0 := by
    simp only [hY, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd.2, one_mul, ← hμdef, sub_self]
  have hYb : ∀ g, |Y g| ≤ 2 * l := fun g => by
    have h₁ := abs_sub (c g) μ
    have := hc g
    simp only [hY]
    linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := t / (4 * l ^ 2) with hs
  have hspos : 0 < s := by positivity
  have hmgf := sum_mul_exp_le hd (by positivity : 0 < 2 * l) hYb hY₀ s
  have hstep : ∀ ω : Fin n → Γ, (if t ≤ (∑ i, c (ω i)) / n then ∏ i, dist (ω i) else 0) ≤
      Real.exp (-(s * (n * t))) * ((∏ i, dist (ω i)) * ∏ i, Real.exp (s * Y (ω i))) := by
    intro ω
    have hw : 0 ≤ ∏ i, dist (ω i) := Finset.prod_nonneg fun i _ => hd.1 _
    have hprod : ∏ i, Real.exp (s * Y (ω i)) = Real.exp (s * ∑ i, Y (ω i)) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    rw [hprod]
    split_ifs with h
    · have hsum : ∑ i, c (ω i) = ∑ i, Y (ω i) + n * μ := by
        simp only [hY, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      rw [le_div_iff₀ hn', hsum] at h
      have hle : n * t ≤ ∑ i, Y (ω i) := by nlinarith
      have h₁ : 1 ≤ Real.exp (-(s * (n * t))) * Real.exp (s * ∑ i, Y (ω i)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      calc ∏ i, dist (ω i) = (∏ i, dist (ω i)) * 1 := (mul_one _).symm
        _ ≤ (∏ i, dist (ω i)) * (Real.exp (-(s * (n * t))) * Real.exp (s * ∑ i, Y (ω i))) :=
          mul_le_mul_of_nonneg_left h₁ hw
        _ = _ := by ring
    · positivity
  calc iidProb dist n (fun ω => t ≤ (∑ i, c (ω i)) / n)
      ≤ ∑ ω : Fin n → Γ, Real.exp (-(s * (n * t))) * ((∏ i, dist (ω i)) * ∏ i, Real.exp (s * Y (ω i))) :=
        Finset.sum_le_sum fun ω _ => hstep ω
    _ = Real.exp (-(s * (n * t))) * ∏ _i : Fin n, ∑ g, dist g * Real.exp (s * Y g) := by
        rw [← Finset.mul_sum, iidProb_sum_prod n fun _ g => Real.exp (s * Y g)]
    _ ≤ Real.exp (-(s * (n * t))) * Real.exp ((s * (2 * l)) ^ 2 / 2) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun g _ =>
          mul_nonneg (hd.1 g) (Real.exp_pos _).le) hmgf n) (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simp only [hs]
        field_simp
        ring

/-! ### A test from contrasts -/

variable {ι : Type*}

/-- The largest mean of the contrasts `c j`, `j ∈ J`, and `0`. -/
def contrastStat (J : Finset ι) (c : ι → Γ → ℝ) {n : ℕ} (ω : Fin n → Γ) : ℝ :=
  J.fold max 0 fun j => (∑ i, c j (ω i)) / n

/-- **A p-value from contrasts of mean at most `0` under the null, bounded by `l`**: Hoeffding's inequality with the union bound. -/
def contrastP (l : ℝ) (J : Finset ι) (c : ι → Γ → ℝ) {n : ℕ} (ω : Fin n → Γ) : ℝ :=
  min 1 (J.card * Real.exp (-(n * contrastStat J c ω ^ 2 / (8 * l ^ 2))))

variable {l : ℝ} {J : Finset ι} {c : ι → Γ → ℝ}

omit [Fintype Γ] in
theorem contrastStat_nonneg {n : ℕ} (ω : Fin n → Γ) : 0 ≤ contrastStat J c ω :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

omit [Fintype Γ] in
theorem contrastP_mem {n : ℕ} (ω : Fin n → Γ) : 0 ≤ contrastP l J c ω ∧ contrastP l J c ω ≤ 1 :=
  ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

/-- **The p-value is valid**, for every `n`: under the null it is below `x` with probability at most `x`. -/
theorem iidProb_contrastP_lt_le (hd : IsDist dist) (hJ : J.Nonempty) (hl : 0 < l)
    (hc : ∀ j ∈ J, ∀ g, |c j g| ≤ l) (hμ : ∀ j ∈ J, ∑ g, dist g * c j g ≤ 0) {x : ℝ} (hx₀ : 0 < x)
    (hx₁ : x < 1) (n : ℕ) : iidProb dist n (fun ω => contrastP l J c ω < x) ≤ x := by
  have hk : (1 : ℝ) ≤ J.card := by exact_mod_cast Finset.card_pos.2 hJ
  have hk₀ : (0 : ℝ) < J.card := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- with no draws the statistic is `0` and the p-value is `1`
    have : iidProb dist 0 (fun ω => contrastP l J c ω < x) = 0 := by
      refine Finset.sum_eq_zero fun ω _ => ite_eq_right fun h => ?_
      have h₁ : contrastP l J c ω = 1 := by
        unfold contrastP
        simp only [CharP.cast_eq_zero, zero_mul, zero_div, neg_zero, Real.exp_zero, mul_one]
        exact min_eq_left hk
      have h' : contrastP l J c ω < x := h
      rw [h₁] at h'
      linarith
    rw [this]
    exact hx₀.le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log (J.card / x) with hL
  have hLpos : 0 < L := Real.log_pos ((one_lt_div hx₀).2 (by linarith))
  set t := Real.sqrt (8 * l ^ 2 * L / n) with ht
  have htpos : 0 < t := Real.sqrt_pos.2 (by positivity)
  have htsq : t ^ 2 = 8 * l ^ 2 * L / n := Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-(n * t ^ 2 / (8 * l ^ 2))) = x / J.card := by
    have : n * t ^ 2 / (8 * l ^ 2) = L := by
      rw [htsq]
      field_simp
    rw [this, hL, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have himp : ∀ ω : Fin n → Γ, contrastP l J c ω < x → ∃ j : J, t ≤ (∑ i, c j.val (ω i)) / n := by
    intro ω hp
    have hp' : (J.card : ℝ) * Real.exp (-(n * contrastStat J c ω ^ 2 / (8 * l ^ 2))) < x := by
      rcases min_lt_iff.1 hp with h | h
      · linarith
      · exact h
    have hlt : t < contrastStat J c ω := by
      by_contra hcon
      push Not at hcon
      have h₀ := contrastStat_nonneg (J := J) (c := c) ω
      have hsq : contrastStat J c ω ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h₀ hcon 2
      have hge : Real.exp (-(n * t ^ 2 / (8 * l ^ 2))) ≤
          Real.exp (-(n * contrastStat J c ω ^ 2 / (8 * l ^ 2))) := by
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hn'.le) (by positivity)
      rw [hexp] at hge
      have : x ≤ (J.card : ℝ) * Real.exp (-(n * contrastStat J c ω ^ 2 / (8 * l ^ 2))) := by
        rw [div_le_iff₀ hk₀] at hge
        linarith
      linarith
    rcases (Finset.lt_fold_max _).1 hlt with h | ⟨j, hj, h⟩
    · linarith
    · exact ⟨⟨j, hj⟩, h.le⟩
  calc iidProb dist n (fun ω => contrastP l J c ω < x)
      ≤ iidProb dist n (fun ω => ∃ j : J, t ≤ (∑ i, c j.val (ω i)) / n) := iidProb_mono hd himp
    _ ≤ ∑ j : J, iidProb dist n (fun ω => t ≤ (∑ i, c j.val (ω i)) / n) := iidProb_exists_le hd _
    _ ≤ ∑ _j : J, x / J.card := Finset.sum_le_sum fun j _ => by
        rw [← hexp]
        exact iidProb_mean_ge_le hd hl (hc j.1 j.2) (hμ j.1 j.2) htpos hn
    _ = x := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        field_simp

/-- **The power of the test**: off the null, the p-value is below `exp(-b_n/2)` for each `b_n = o(n)`. -/
theorem tendsto_contrastP_lt (hd : IsDist dist) (hl : 0 < l) {j₀ : ι} (hj₀ : j₀ ∈ J)
    (hμ : 0 < ∑ g, dist g * c j₀ g) {b : ℕ → ℝ} (hb : Tendsto (fun n : ℕ => b n / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      contrastP l J c ω < Real.exp (-(b n) / 2)) atTop (𝓝 1) := by
  set μ := ∑ g, dist g * c j₀ g with hμdef
  have hlln := iidProb_weak_law hd (c j₀) (half_pos hμ)
  set κ : ℝ := (μ / 2) ^ 2 / (8 * l ^ 2) with hκ
  have hκpos : 0 < κ := by positivity
  have hk₀ : (0 : ℝ) < J.card := by exact_mod_cast Finset.card_pos.2 ⟨j₀, hj₀⟩
  have hb' := QuartetTests.eventually_le_mul hb hκpos
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log J.card < n * (κ / 2) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) * (κ / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    exact h.eventually_gt_atTop _
  refine tendsto_iidProb_of_imp hd ?_ hlln
  filter_upwards [hb', hlog] with n h₁ h₂ ω hω
  have hmean := (abs_lt.1 hω).1
  have hT : μ / 2 < contrastStat J c ω :=
    (Finset.lt_fold_max _).2 (Or.inr ⟨j₀, hj₀, by linarith⟩)
  have hsq : (μ / 2) ^ 2 ≤ contrastStat J c ω ^ 2 := pow_le_pow_left₀ (by positivity) hT.le 2
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hle : (J.card : ℝ) * Real.exp (-(n * contrastStat J c ω ^ 2 / (8 * l ^ 2))) ≤
      (J.card : ℝ) * Real.exp (-(n * κ)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hk₀.le
    rw [hκ, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hn₀) (by positivity)
  have hlt : (J.card : ℝ) * Real.exp (-(n * κ)) < Real.exp (-(b n) / 2) := by
    have heq : (J.card : ℝ) * Real.exp (-(n * κ)) = Real.exp (Real.log J.card + -(n * κ)) := by
      rw [Real.exp_add, Real.exp_log hk₀]
    rw [heq]
    refine Real.exp_lt_exp.2 ?_
    nlinarith
  exact (min_le_right _ _).trans_lt (hle.trans_lt hlt)

/-- From validity of finitely many p-values to the bound under the null that `Framework.AdequateTests` asks. -/
theorem exists_delta_of_valid (hd : IsDist dist) {κ : Type*} [Fintype κ] {Null : κ → Prop}
    {f : κ → (n : ℕ) → (Fin n → Γ) → ℝ}
    (h : ∀ i, Null i → ∀ x : ℝ, 0 < x → x < 1 → ∀ n, iidProb dist n (fun ω => f i n ω < x) ≤ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ n, 1 - ε < iidProb dist n fun ω => ∀ i, Null i → δ ≤ f i n ω := by
  set K : ℝ := (Fintype.card κ : ℝ) with hK
  have hK₀ : 0 ≤ K := Nat.cast_nonneg _
  set δ := min (1 / 4) (ε / (K + 1)) with hδ
  have hδ₀ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 / 4 := min_le_left _ _
  have hδ₂ : δ ≤ ε / (K + 1) := min_le_right _ _
  refine ⟨δ, hδ₀, by linarith, fun n => ?_⟩
  have hbad : iidProb dist n (fun ω => ∃ i, Null i ∧ f i n ω < δ) ≤ K * δ := by
    calc iidProb dist n (fun ω => ∃ i, Null i ∧ f i n ω < δ)
        ≤ ∑ i, iidProb dist n (fun ω => Null i ∧ f i n ω < δ) := iidProb_exists_le hd _
      _ ≤ ∑ _i : κ, δ := Finset.sum_le_sum fun i _ => by
          by_cases hi : Null i
          · refine le_trans (iidProb_mono hd fun ω hω => hω.2) (h i hi δ hδ₀ (by linarith) n)
          · have : iidProb dist n (fun ω => Null i ∧ f i n ω < δ) = 0 :=
              Finset.sum_eq_zero fun ω _ => ite_eq_right fun h' => absurd h'.1 hi
            rw [this]
            exact hδ₀.le
      _ = K * δ := by simp [hK]
  have hnot := iidProb_not hd n fun ω => ∃ i, Null i ∧ f i n ω < δ
  have hle : iidProb dist n (fun ω => ¬ ∃ i, Null i ∧ f i n ω < δ) ≤
      iidProb dist n fun ω => ∀ i, Null i → δ ≤ f i n ω :=
    iidProb_mono hd fun ω hω i hi => by
      by_contra hcon
      exact hω ⟨i, hi, not_le.1 hcon⟩
  have hKδ : K * δ < ε := by
    have h₁ : K * δ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hδ₂ hK₀
    have h₂ : K * (ε / (K + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith

end Hoeffding

/-! ### Sums of pairs -/

section Sums

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The distance on the two taxa of `P`, for a symmetric function vanishing on the diagonal. -/
def pairSum (D : X → X → ℝ) (P : Finset X) : ℝ := (∑ x ∈ P, ∑ y ∈ P, D x y) / 2

/-- **The sum of pairs of the quartet tree `s`**: `SP_xy|zt = D(x,y) + D(z,t)`. -/
def spOf (D : X → X → ℝ) (s : QuartetTree X) : ℝ := ∑ P ∈ s.val, pairSum D P

omit [Fintype X] in
theorem pairSum_pair {D : X → X → ℝ} (hs : ∀ x y, D x y = D y x) (h0 : ∀ x, D x x = 0) {a b : X} (hab : a ≠ b) :
    pairSum D {a, b} = D a b := by
  unfold pairSum
  rw [Finset.sum_pair hab, Finset.sum_pair hab, Finset.sum_pair hab, h0, h0, hs b a]
  ring

omit [Fintype X] in
/-- The sum of pairs on a tuple is the library's. -/
theorem spOf_quartetTree {D : X → X → ℝ} (hs : ∀ x y, D x y = D y x) (h0 : ∀ x, D x x = 0) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    spOf D (quartetTree a b c d h) = FourPoint.sumOfPairs D a b c d := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have hne : ({a, b} : Finset X) ≠ {c, d} := by
    intro he
    have : a ∈ ({c, d} : Finset X) := he ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact hac h'
    · exact had h'
  unfold spOf
  rw [quartetTree_val, Finset.sum_pair hne, pairSum_pair hs h0 hab, pairSum_pair hs h0 hcd]
  rfl

omit [Fintype X] [DecidableEq X] in
/-- The distance on a pair is linear in the distance. -/
theorem pairSum_sum {κ : Type*} [Fintype κ] (w : κ → ℝ) (d : κ → X → X → ℝ) (P : Finset X) :
    pairSum (fun x y => ∑ g, w g * d g x y) P = ∑ g, w g * pairSum (d g) P := by
  unfold pairSum
  have h₁ : ∀ x, ∑ y ∈ P, ∑ g, w g * d g x y = ∑ g, ∑ y ∈ P, w g * d g x y := fun x => Finset.sum_comm
  simp only [h₁]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_div_assoc', Finset.mul_sum]
  simp only [Finset.mul_sum]

omit [Fintype X] in
/-- The sum of pairs is linear in the distance. -/
theorem spOf_sum {κ : Type*} [Fintype κ] (w : κ → ℝ) (d : κ → X → X → ℝ) (s : QuartetTree X) :
    spOf (fun x y => ∑ g, w g * d g x y) s = ∑ g, w g * spOf (d g) s := by
  unfold spOf
  simp only [pairSum_sum, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype X] in
theorem abs_spOf_le {D : X → X → ℝ} {B : ℝ} (hB : ∀ x y, |D x y| ≤ B) (s : QuartetTree X) :
    |spOf D s| ≤ 4 * B := by
  have hP : ∀ P ∈ s.val, |pairSum D P| ≤ 2 * B := by
    intro P hP
    have hc : P.card = 2 := s.card_of_mem hP
    unfold pairSum
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    calc |∑ x ∈ P, ∑ y ∈ P, D x y| ≤ ∑ x ∈ P, ∑ y ∈ P, |D x y| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _x ∈ P, ∑ _y ∈ P, B := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hB x y
      _ = 2 * B * 2 := by
          simp only [Finset.sum_const, hc, nsmul_eq_mul]
          push_cast
          ring
  calc |spOf D s| ≤ ∑ P ∈ s.val, |pairSum D P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _P ∈ s.val, 2 * B := Finset.sum_le_sum hP
    _ = 4 * B := by
        rw [Finset.sum_const, s.2.1, nsmul_eq_mul]
        push_cast
        ring

/-- The analogue of (5.2): `SP_ab|cd < SP_ac|bd = SP_ad|bc`. -/
def IsSPStrict (D : X → X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, spOf D s < spOf D r) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
    spOf D r = spOf D r'

/-- The analogue of the T1 null: `SP_ab|cd ≤ SP_ac|bd = SP_ad|bc`. -/
def IsSPNull (D : X → X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, spOf D s ≤ spOf D r) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
    spOf D r = spOf D r'

/-- The analogue of (5.1): the three sums of pairs on `q` are equal. -/
def IsSPStar (D : X → X → ℝ) (q : Finset X) : Prop :=
  ∀ r ∈ treesOn q, ∀ r' ∈ treesOn q, spOf D r = spOf D r'

variable {V E : Type*}

/-- **The analogue of Assumption 1 for distances, its forward direction.** -/
structure SPForward (N : RootedNetwork V E X) (D : X → X → ℝ) : Prop where
  star : ∀ q : Finset X, q.card = 4 → HasTrivialFourBlob N q → IsSPStar D q
  t1 : ∀ s : QuartetTree X, InducedCutSplit N s → IsSPStrict D s

/-- **The analogue of Assumption 1 for distances, its converse direction.** -/
structure SPConverse (N : RootedNetwork V E X) (D : X → X → ℝ) : Prop where
  star : ∀ q : Finset X, q.card = 4 → ¬ HasTrivialFourBlob N q → ¬ IsSPStar D q
  t1 : ∀ s : QuartetTree X, ¬ InducedCutSplit N s → ¬ IsSPStrict D s

variable {N : RootedNetwork V E X} {D : X → X → ℝ}

/-- By both directions, the analogue of the T1 null holds exactly on a cut split or a trivial 4-blob. -/
theorem isSPNull_iff (hF : SPForward N D) (hC : SPConverse N D) (s : QuartetTree X) :
    IsSPNull D s ↔ IsNullQuartet N s := by
  have hmem : ∀ r ∈ s.alternatives, r ∈ treesOn s.taxa := fun r hr =>
    QuartetTests.mem_treesOn_taxa_of_mem_alternatives hr
  constructor
  · rintro ⟨hle, heq⟩
    by_contra hcon
    unfold IsNullQuartet at hcon
    push Not at hcon
    have hns := hC.t1 s hcon.1
    have hnt := hC.star _ s.card_taxa hcon.2
    have hstrict : ¬ ∀ r ∈ s.alternatives, spOf D s < spOf D r := fun h => hns ⟨h, heq⟩
    push Not at hstrict
    obtain ⟨r₀, hr₀, hr₀'⟩ := hstrict
    have hs₀ : spOf D s = spOf D r₀ := le_antisymm (hle r₀ hr₀) hr₀'
    apply hnt
    have hall : ∀ r ∈ treesOn s.taxa, spOf D r = spOf D s := by
      intro r hr
      by_cases hrs : r = s
      · rw [hrs]
      · have hra : r ∈ s.alternatives := QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hrs⟩
        rw [heq r hra r₀ hr₀, hs₀]
    intro r hr r' hr'
    rw [hall r hr, hall r' hr']
  · rintro (h | h)
    · exact ⟨fun r hr => ((hF.t1 s h).1 r hr).le, (hF.t1 s h).2⟩
    · have hst := hF.star _ s.card_taxa h
      have hsm := QuartetTests.mem_treesOn_taxa s
      exact ⟨fun r hr => (hst s hsm r (hmem r hr)).le, fun r hr r' hr' => hst r (hmem r hr) r' (hmem r' hr')⟩

/-- The converse, from what happens on each set of four taxa: a trivial 4-blob, a cut split, or three trees of which one has the
strictly largest sum of pairs, which is item 2 of Proposition 6.1 of Rhodes et al. 2025. -/
theorem spConverse_of_cases (hF : SPForward N D)
    (h : ∀ q : Finset X, q.card = 4 → HasTrivialFourBlob N q ∨ (∃ s ∈ treesOn q, InducedCutSplit N s) ∨
      ∃ s₁ ∈ treesOn q, ∃ s₂ ∈ treesOn q, ∃ s₃ ∈ treesOn q,
        s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ ∧ spOf D s₁ < spOf D s₃ ∧ spOf D s₂ < spOf D s₃) :
    SPConverse N D := by
  refine ⟨fun q hq htr hu => ?_, fun s hs hstrict => ?_⟩
  · rcases h q hq with h' | ⟨s, hsq, hc⟩ | ⟨s₁, h₁, s₂, _, s₃, h₃, _, _, _, h₁₃, _⟩
    · exact htr h'
    · have hq' : s.taxa = q := mem_treesOn.1 hsq
      obtain ⟨r, hr⟩ : s.alternatives.Nonempty := by
        rw [← Finset.card_pos, s.card_alternatives]
        omega
      have hlt := (hF.t1 s hc).1 r hr
      rw [hu s hsq r (hq' ▸ QuartetTests.mem_treesOn_taxa_of_mem_alternatives hr)] at hlt
      exact lt_irrefl _ hlt
    · exact h₁₃.ne (hu s₁ h₁ s₃ h₃)
  · rcases h s.taxa s.card_taxa with h' | ⟨s₀, hs₀, hc⟩ | ⟨s₁, h₁, s₂, h₂, s₃, h₃, h12, h13, h23, h₁₃, h₂₃⟩
    · obtain ⟨r, hr⟩ : s.alternatives.Nonempty := by
        rw [← Finset.card_pos, s.card_alternatives]
        omega
      have hlt := hstrict.1 r hr
      rw [hF.star _ s.card_taxa h' s (QuartetTests.mem_treesOn_taxa s) r
        (QuartetTests.mem_treesOn_taxa_of_mem_alternatives hr)] at hlt
      exact lt_irrefl _ hlt
    · have hne : s₀ ≠ s := fun he => hs (he ▸ hc)
      have htaxa : s₀.taxa = s.taxa := mem_treesOn.1 hs₀
      have h₁ := hstrict.1 s₀ (QuartetTree.mem_alternatives.2 ⟨htaxa, hne⟩)
      have h₂ := (hF.t1 s₀ hc).1 s (QuartetTree.mem_alternatives.2 ⟨htaxa.symm, hne.symm⟩)
      exact lt_asymm h₁ h₂
    · have hall : treesOn s.taxa = {s₁, s₂, s₃} := by
        symm
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro r hr
          simp only [mem_insert, mem_singleton] at hr
          rcases hr with rfl | rfl | rfl <;> assumption
        · rw [card_treesOn s.card_taxa, Finset.card_eq_three.2 ⟨s₁, s₂, s₃, h12, h13, h23, rfl⟩]
      have hsm := QuartetTests.mem_treesOn_taxa s
      rw [hall] at hsm
      simp only [mem_insert, mem_singleton] at hsm
      have halt : ∀ {r : QuartetTree X}, r ∈ treesOn s.taxa → r ≠ s → r ∈ s.alternatives := fun hr hne =>
        QuartetTree.mem_alternatives.2 ⟨mem_treesOn.1 hr, hne⟩
      rcases hsm with rfl | rfl | rfl
      · exact h₂₃.ne (hstrict.2 s₂ (halt h₂ h12.symm) s₃ (halt h₃ h13.symm))
      · exact h₁₃.ne (hstrict.2 s₁ (halt h₁ h12) s₃ (halt h₃ h23.symm))
      · exact lt_asymm (hstrict.1 s₁ (halt h₁ h13)) h₁₃

/-- A side of the tree of blobs of `N₁` is one of `N₂`, with the same distance: by Theorem 4.1 (`ECToBlob.corollary4_2`), a side
that is not a cut split has a quartet that is not, and this quartet has the form (5.2) if the side is one of `N₁`. -/
theorem treeOfBlobs_subset_of_sp {V₁ E₁ V₂ E₂ : Type*} {N₁ : RootedNetwork V₁ E₁ X}
    {N₂ : RootedNetwork V₂ E₂ X} (h₁ : N₁.IsPhylogenetic) (h₂ : N₂.IsPhylogenetic)
    (hF₁ : SPForward N₁ D) (hC₂ : SPConverse N₂ D) : treeOfBlobs N₁ ⊆ treeOfBlobs N₂ := by
  intro A hA
  obtain ⟨_, hne, hne', _⟩ := mem_filter.1 hA
  by_cases hint : 2 ≤ A.card ∧ 2 ≤ Aᶜ.card
  · refine mem_filter.2 ⟨mem_univ _, hne, hne', ?_⟩
    rcases corollary4_2 h₂ A hint.1 hint.2 with h | h
    · exact h
    · exfalso
      obtain ⟨a₁, ha₁⟩ := hne
      obtain ⟨b₁, hb₁⟩ := hne'
      obtain ⟨a₂, ha₂, b₂, hb₂, hane, hbne, hnot⟩ := h a₁ ha₁ b₁ hb₁
      have hAB : ∀ {a b : X}, a ∈ A → b ∈ Aᶜ → a ≠ b := fun ha hb hab =>
        Finset.mem_compl.mp hb (hab ▸ ha)
      have h4 : ({a₁, a₂, b₁, b₂} : Finset X).card = 4 :=
        TreeMetric.card_four_of_ne hane.symm (hAB ha₁ hb₁) (hAB ha₁ hb₂) (hAB ha₂ hb₁) (hAB ha₂ hb₂)
          hbne.symm
      have hb₁' : b₁ ∉ A := Finset.mem_compl.1 hb₁
      have hb₂' : b₂ ∉ A := Finset.mem_compl.1 hb₂
      have hin : A ∩ (quartetTree a₁ a₂ b₁ b₂ h4).taxa ∈ (quartetTree a₁ a₂ b₁ b₂ h4).val := by
        rw [FalseEdge.taxa_quartetTree, FalseEdge.inter_four ha₁ ha₂ hb₁' hb₂']
        simp
      have hstrict := hF₁.t1 _ (inducedCutSplit_of_mem h₁ hA hin)
      have hcut₂ : InducedCutSplit N₂ (quartetTree a₁ a₂ b₁ b₂ h4) := by
        by_contra hcon
        exact hC₂.t1 _ hcon hstrict
      exact hnot (FalseEdge.hasCutSplitOn_of_inducedCutSplit h4 hcut₂)
  · exact mem_treeOfBlobs_of_not_internal h₂ hne hne' hint

/-- (`ecto:sec10_sp_identifiable`) **"The tree of blobs is identifiable from average pairwise distances"** (line 1429), under the analogue of Assumption 1: two
networks with the same distance have the same tree of blobs. -/
theorem treeOfBlobs_eq_of_eq {V' E' : Type*} {N' : RootedNetwork V' E' X} (hN : N.IsPhylogenetic)
    (hN' : N'.IsPhylogenetic) (hF : SPForward N D) (hC : SPConverse N D) (hF' : SPForward N' D)
    (hC' : SPConverse N' D) : treeOfBlobs N = treeOfBlobs N' :=
  Finset.Subset.antisymm (treeOfBlobs_subset_of_sp hN hN' hF hC') (treeOfBlobs_subset_of_sp hN' hN hF' hC)

end Sums

/-! ### A test for distances -/

section Test

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : Type*} [Fintype Γ]

/-- The contrast of two quartet trees at a gene tree. -/
def contrast (d : Γ → X → X → ℝ) (p : QuartetTree X × QuartetTree X) (g : Γ) : ℝ :=
  spOf (d g) p.1 - spOf (d g) p.2

/-- The contrasts of the star test on `q`: all ordered pairs of trees on `q`. -/
def starPairs (q : Finset X) : Finset (QuartetTree X × QuartetTree X) := (treesOn q).offDiag

/-- The contrasts of the T1 test on `s`: `s` against each alternative, and the alternatives against each other. -/
def t1Pairs (s : QuartetTree X) : Finset (QuartetTree X × QuartetTree X) :=
  s.alternatives.offDiag ∪ s.alternatives.image fun r => (s, r)

/-- **The star p-value on distances.** -/
def spStarP (l : ℝ) (d : Γ → X → X → ℝ) (s : QuartetTree X) (n : ℕ) (ω : Fin n → Γ) : ℝ :=
  contrastP l (starPairs s.taxa) (contrast d) ω

/-- **The T1 p-value on distances.** -/
def spT1P (l : ℝ) (d : Γ → X → X → ℝ) (s : QuartetTree X) (n : ℕ) (ω : Fin n → Γ) : ℝ :=
  contrastP l (t1Pairs s) (contrast d) ω

variable {V E : Type*} {N : RootedNetwork V E X} {dist : Γ → ℝ} {d : Γ → X → X → ℝ} {B : ℝ}

/-- The distance `D`, the mean of the distances of the gene trees. -/
def meanDist (dist : Γ → ℝ) (d : Γ → X → X → ℝ) (x y : X) : ℝ := ∑ g, dist g * d g x y

omit [Fintype X] in
theorem sum_contrast (dist : Γ → ℝ) (d : Γ → X → X → ℝ) (p : QuartetTree X × QuartetTree X) :
    ∑ g, dist g * contrast d p g = spOf (meanDist dist d) p.1 - spOf (meanDist dist d) p.2 := by
  unfold meanDist contrast
  rw [spOf_sum, spOf_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun g _ => by ring

omit [Fintype X] [Fintype Γ] in
theorem abs_contrast_le (hb : ∀ g x y, |d g x y| ≤ B) (p : QuartetTree X × QuartetTree X) (g : Γ) :
    |contrast d p g| ≤ 8 * B := by
  have h₁ := abs_spOf_le (hb g) p.1
  have h₂ := abs_spOf_le (hb g) p.2
  have := abs_sub (spOf (d g) p.1) (spOf (d g) p.2)
  unfold contrast
  linarith

/-- **The test is adequate for Bon and BBC**, at any levels with `o(n)` cutoffs, for a model with the analogue of Assumption 1.
Its p-values are not bounded away from `1` under the null, and they are valid for every `n`. -/
theorem adequateTests_sumOfPairs (hd : IsDist dist) (hB : 0 < B) (hb : ∀ g x y, |d g x y| ≤ B)
    (hF : SPForward N (meanDist dist d)) (hC : SPConverse N (meanDist dist d)) {m : TestCorrection}
    (hm : m = .bon ∨ m = .bbc) {α β : ℕ → ℝ} (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (hβpos : ∀ᶠ n in atTop, 0 < β n)
    (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    AdequateTests N dist m α β (spStarP (8 * B) d) (spT1P (8 * B) d) := by
  have hl : 0 < 8 * B := by positivity
  have hno : ¬ (m = .cauchy ∨ m = .cbc) := by
    rcases hm with rfl | rfl <;> simp
  have hstarNe : ∀ s : QuartetTree X, (starPairs s.taxa).Nonempty := by
    intro s
    obtain ⟨r, hr, r', hr', hne⟩ := Finset.one_lt_card.1
      (by rw [card_treesOn s.card_taxa]; norm_num : 1 < (treesOn s.taxa).card)
    exact ⟨(r, r'), Finset.mem_offDiag.2 ⟨hr, hr', hne⟩⟩
  have ht1Ne : ∀ s : QuartetTree X, (t1Pairs s).Nonempty := by
    intro s
    obtain ⟨r, hr⟩ : s.alternatives.Nonempty := by
      rw [← Finset.card_pos, s.card_alternatives]
      omega
    exact ⟨(s, r), Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, hr, rfl⟩)⟩
  refine ⟨fun s n ω => contrastP_mem ω, fun s n ω => contrastP_mem ω, fun ε hε => ?_,
    fun s hs c hc => ?_, fun ε hε => ?_, fun s hs c hc => ?_⟩
  · obtain ⟨δ, h0, h1, hev⟩ := exists_delta_of_valid hd
      (Null := fun s : QuartetTree X => HasTrivialFourBlob N s.taxa) (f := spStarP (8 * B) d)
      (fun s hs x hx₀ hx₁ n => iidProb_contrastP_lt_le hd (hstarNe s) hl
        (fun p _ g => abs_contrast_le hb p g) (fun p hp => by
          obtain ⟨hp₁, hp₂, _⟩ := Finset.mem_offDiag.1 hp
          rw [sum_contrast, hF.star _ s.card_taxa hs p.1 hp₁ p.2 hp₂, sub_self]) hx₀ hx₁ n) hε
    refine ⟨δ, h0, h1, Eventually.of_forall fun n => (hev n).trans_le (iidProb_mono hd fun ω hω s hs => ?_)⟩
    exact ⟨hω s hs, fun h => absurd h hno⟩
  · refine tendsto_lt_level_of_growth hβpos hβ (fun b hb' => ?_) hc
    have hnst := hC.star _ s.card_taxa hs
    unfold IsSPStar at hnst
    push Not at hnst
    obtain ⟨r, hr, r', hr', hne⟩ := hnst
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine tendsto_contrastP_lt hd hl (j₀ := (r', r))
        (Finset.mem_offDiag.2 ⟨hr', hr, fun h => hne (by rw [show r' = r from h])⟩) ?_ hb'
      rw [sum_contrast]
      simpa using hlt
    · refine tendsto_contrastP_lt hd hl (j₀ := (r, r'))
        (Finset.mem_offDiag.2 ⟨hr, hr', fun h => hne (by rw [show r = r' from h])⟩) ?_ hb'
      rw [sum_contrast]
      simpa using hlt
  · obtain ⟨δ, h0, h1, hev⟩ := exists_delta_of_valid hd
      (Null := fun s : QuartetTree X => IsNullQuartet N s) (f := spT1P (8 * B) d)
      (fun s hs x hx₀ hx₁ n => iidProb_contrastP_lt_le hd (ht1Ne s) hl
        (fun p _ g => abs_contrast_le hb p g) (fun p hp => by
          obtain ⟨hle, heq⟩ := (isSPNull_iff hF hC s).2 hs
          rw [sum_contrast]
          rcases Finset.mem_union.1 hp with hp | hp
          · obtain ⟨hp₁, hp₂, _⟩ := Finset.mem_offDiag.1 hp
            rw [heq p.1 hp₁ p.2 hp₂, sub_self]
          · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
            exact sub_nonpos.2 (hle r hr)) hx₀ hx₁ n) hε
    refine ⟨δ, h0, h1, Eventually.of_forall fun n => (hev n).trans_le (iidProb_mono hd fun ω hω s hs => ?_)⟩
    exact ⟨hω s hs, fun h => absurd h hno⟩
  · refine tendsto_lt_level_of_growth hαpos hα (fun b hb' => ?_) hc
    have hnull : ¬ IsSPNull (meanDist dist d) s := fun h => hs ((isSPNull_iff hF hC s).1 h)
    unfold IsSPNull at hnull
    by_cases hle : ∀ r ∈ s.alternatives, spOf (meanDist dist d) s ≤ spOf (meanDist dist d) r
    · have hne : ¬ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives,
          spOf (meanDist dist d) r = spOf (meanDist dist d) r' := fun h => hnull ⟨hle, h⟩
      push Not at hne
      obtain ⟨r, hr, r', hr', hrne⟩ := hne
      rcases lt_or_gt_of_ne hrne with hlt | hlt
      · refine tendsto_contrastP_lt hd hl (j₀ := (r', r)) (Finset.mem_union_left _
          (Finset.mem_offDiag.2 ⟨hr', hr, fun h => hrne (by rw [show r' = r from h])⟩)) ?_ hb'
        rw [sum_contrast]
        simpa using hlt
      · refine tendsto_contrastP_lt hd hl (j₀ := (r, r')) (Finset.mem_union_left _
          (Finset.mem_offDiag.2 ⟨hr, hr', fun h => hrne (by rw [show r = r' from h])⟩)) ?_ hb'
        rw [sum_contrast]
        simpa using hlt
    · push Not at hle
      obtain ⟨r, hr, hlt⟩ := hle
      refine tendsto_contrastP_lt hd hl (j₀ := (s, r)) (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨r, hr, rfl⟩)) ?_ hb'
      rw [sum_contrast]
      simpa using hlt

/-- (`ecto:sec10_sp_test`) **Lines 1419-1432: the framework on distances.** For a sample of `n` loci with bounded distances `d`, of mean `D`, with the
analogue of Assumption 1 for `D`: the output of the algorithm on the p-values `spStarP` and `spT1P`, with Bon or BBC, is the tree of
blobs with probability tending to one, at any levels with `o(n)` cutoffs. -/
theorem consistency_sumOfPairs (hN : N.IsPhylogenetic) (hd : IsDist dist) (hB : 0 < B)
    (hb : ∀ g x y, |d g x y| ≤ B) (hF : SPForward N (meanDist dist d))
    (hC : SPConverse N (meanDist dist d)) {T₀ : Finset (Finset X)}
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) {o : ECToBlobOptions}
    (hm : o.testCo = .bon ∨ o.testCo = .bbc) {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝[>] 0))
    (hβ₀ : Tendsto β atTop (𝓝[>] 0)) (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb dist n fun ω =>
      ectoblobBy o (α n) (β n) (fun s => spStarP (8 * B) d s n ω) (fun s => spT1P (8 * B) d s n ω) T₀ =
        treeOfBlobs N) atTop (𝓝 1) :=
  consistency_ectoblobBy hN hd hα₀ hβ₀
    (adequateTests_sumOfPairs hd hB hb hF hC hm (hα₀.eventually self_mem_nhdsWithin)
      (hβ₀.eventually self_mem_nhdsWithin) hα hβ) hT₀ rfl

end Test

/-! ### The average distance of the displayed tree model -/

section Average

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
  {N : RootedNetwork V E X} {θ : MetricData E}

/-- `1` if the cluster `C` separates `x` from `y`. -/
def arcSep (C : Finset X) (x y : X) : ℝ := if (x ∈ C ∧ y ∉ C) ∨ (y ∈ C ∧ x ∉ C) then 1 else 0

variable (N θ) in
/-- **The path length between two taxa in the tree displayed by a parent choice**: the kept arcs that separate them. -/
def displayedDist (c : N.ParentChoice) (x y : X) : ℝ :=
  ∑ f, if f ∉ N.deletedArcs c then θ.length f * arcSep (N.displayedCluster c (N.graph.target f)) x y else 0

variable (N θ) in
/-- **The average distance under the displayed tree model** (Rhodes et al. 2025, equations (1) and (2)): the mixture over the
displayed trees. -/
def averageDist (x y : X) : ℝ := meanDist (N.choiceWeight θ) (displayedDist N θ) x y

/-- The cluster `C` has the pattern `ab|cd` on four taxa. -/
def IsPat (C : Finset X) (a b c d : X) : Prop :=
  (a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ d ∉ C) ∨ (c ∈ C ∧ d ∈ C ∧ a ∉ C ∧ b ∉ C)

variable (N θ) in
/-- The total length of the kept arcs with the pattern `ab|cd`: the internal edge of `ab|cd` in the displayed tree. -/
def patWeight (c : N.ParentChoice) (a b d e : X) : ℝ :=
  ∑ f, if f ∉ N.deletedArcs c ∧ IsPat (N.displayedCluster c (N.graph.target f)) a b d e then θ.length f else 0

variable (N θ) in
/-- The mixture of `patWeight` over the displayed trees. -/
def avgWeight (a b d e : X) : ℝ := ∑ c, N.choiceWeight θ c * patWeight N θ c a b d e

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem isPat_comm_left {C : Finset X} {a b d e : X} : IsPat C a b d e ↔ IsPat C b a d e := by
  unfold IsPat
  tauto

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem isPat_comm_right {C : Finset X} {a b d e : X} : IsPat C a b d e ↔ IsPat C a b e d := by
  unfold IsPat
  tauto

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The identity for one arc: `δ(a,c) + δ(b,d) - δ(a,b) - δ(c,d)` is twice the pattern `ab|cd` less twice the pattern `ac|bd`. -/
theorem arcSep_identity (C : Finset X) (a b d e : X) :
    arcSep C a d + arcSep C b e - arcSep C a b - arcSep C d e =
      2 * (if IsPat C a b d e then 1 else 0) - 2 * (if IsPat C a d b e then 1 else 0) := by
  unfold arcSep IsPat
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> by_cases hd : d ∈ C <;> by_cases he : e ∈ C <;>
    simp [ha, hb, hd, he] <;> norm_num

omit [Fintype V] in
/-- The identity on a displayed tree. -/
theorem displayedDist_identity (c : N.ParentChoice) (a b d e : X) :
    displayedDist N θ c a d + displayedDist N θ c b e - displayedDist N θ c a b - displayedDist N θ c d e =
      2 * patWeight N θ c a b d e - 2 * patWeight N θ c a d b e := by
  unfold displayedDist patWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hid := arcSep_identity (N.displayedCluster c (N.graph.target f)) a b d e
  by_cases hk : f ∉ N.deletedArcs c
  · simp only [hk, not_false_eq_true, true_and, ite_true]
    by_cases h₁ : IsPat (N.displayedCluster c (N.graph.target f)) a b d e <;>
      by_cases h₂ : IsPat (N.displayedCluster c (N.graph.target f)) a d b e <;>
      simp only [h₁, h₂, ite_true, ite_false] at hid ⊢ <;> linear_combination θ.length f * hid
  · simp [hk]

/-- **The identity for the average distance**: `SP_ac|bd - SP_ab|cd = 2 W(ab|cd) - 2 W(ac|bd)`. -/
theorem sumOfPairs_sub_eq (a b d e : X) :
    averageDist N θ a d + averageDist N θ b e - averageDist N θ a b - averageDist N θ d e =
      2 * avgWeight N θ a b d e - 2 * avgWeight N θ a d b e := by
  unfold averageDist meanDist avgWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  linear_combination N.choiceWeight θ c * displayedDist_identity (N := N) (θ := θ) c a b d e

omit [Fintype V] [Fintype E] [Fintype X] in
theorem arcSep_comm (C : Finset X) (x y : X) : arcSep C x y = arcSep C y x := by
  unfold arcSep
  simp only [or_comm]

theorem averageDist_comm (x y : X) : averageDist N θ x y = averageDist N θ y x := by
  unfold averageDist meanDist displayedDist
  simp only [arcSep_comm _ x y]

theorem averageDist_self (x : X) : averageDist N θ x x = 0 := by
  unfold averageDist meanDist displayedDist arcSep
  simp

omit [DecidableEq X] in
theorem avgWeight_comm_left (a b d e : X) : avgWeight N θ a b d e = avgWeight N θ b a d e := by
  unfold avgWeight patWeight
  simp only [isPat_comm_left (a := a) (b := b)]

omit [DecidableEq X] in
theorem avgWeight_comm_right (a b d e : X) : avgWeight N θ a b d e = avgWeight N θ a b e d := by
  unfold avgWeight patWeight
  simp only [isPat_comm_right (d := d) (e := e)]

omit [Fintype V] [Fintype E] in
/-- A kept arc with a pattern makes the tree of the choice display the quartet tree. -/
theorem displays_of_isPat [Fintype V] {c : N.ParentChoice} {u : V} {a b d e : X}
    (h : ({a, b, d, e} : Finset X).card = 4) (hp : IsPat (N.displayedCluster c u) a b d e) :
    Displays (N.displayedSides c) (quartetTree a b d e h) := by
  rcases hp with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · refine Section3Observations.displays_of_cluster (P := {a, b}) (u := u) (by simp) (fun x hx => ?_)
      (fun x hx hxP => ?_)
    · rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [FalseEdge.taxa_quartetTree] at hx
      simp only [mem_insert, mem_singleton, not_or] at hx hxP
      rcases hx with rfl | rfl | rfl | rfl
      · exact absurd rfl hxP.1
      · exact absurd rfl hxP.2
      · exact h₃
      · exact h₄
  · refine Section3Observations.displays_of_cluster (P := {d, e}) (u := u) (by simp) (fun x hx => ?_)
      (fun x hx hxP => ?_)
    · rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [FalseEdge.taxa_quartetTree] at hx
      simp only [mem_insert, mem_singleton, not_or] at hx hxP
      rcases hx with rfl | rfl | rfl | rfl
      · exact h₃
      · exact h₄
      · exact absurd rfl hxP.1
      · exact absurd rfl hxP.2

variable [Nonempty X]

/-- If the tree of a choice displays another quartet tree on the four taxa, then no kept arc has the pattern. -/
theorem patWeight_eq_zero (hN : N.IsPhylogenetic) {c : N.ParentChoice} {a b d e : X}
    (h : ({a, b, d, e} : Finset X).card = 4) {r : QuartetTree X} (hr : Displays (N.displayedSides c) r)
    (ht : r.taxa = {a, b, d, e}) (hne : quartetTree a b d e h ≠ r) : patWeight N θ c a b d e = 0 := by
  refine Finset.sum_eq_zero fun f _ => ite_eq_right ?_
  rintro ⟨-, hp⟩
  exact absurd ((isUnrootedTree_displayedSides hN c).displays_unique (displays_of_isPat h hp) hr
    (by rw [ht, FalseEdge.taxa_quartetTree])) hne

omit [DecidableEq X] [Nonempty X] in
/-- `avgWeight` is positive, from one kept arc with the pattern of positive length, at valid parameters. -/
theorem avgWeight_pos [DecidableEq X] (hθ : N.IsMetric θ) (c : N.ParentChoice) {f : E}
    (hf : f ∉ N.deletedArcs c) {a b d e : X} (hp : IsPat (N.displayedCluster c (N.graph.target f)) a b d e)
    (hl : 0 < θ.length f) : 0 < avgWeight N θ a b d e := by
  have hw := hθ.isWeakMetric
  have hnn : ∀ (c' : N.ParentChoice), 0 ≤ patWeight N θ c' a b d e := fun c' =>
    Finset.sum_nonneg fun g _ => by
      split_ifs
      · exact hw.1 g
      · exact le_rfl
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (fun c' _ => mul_nonneg (choiceWeight_nonneg hw c') (hnn c')) (by simp : c ∈ _))
  refine mul_pos (prod_pos fun _ _ => NMSC.inheritance_pos hθ _) ?_
  refine lt_of_lt_of_le hl ?_
  have := Finset.single_le_sum (f := fun g => if g ∉ N.deletedArcs c ∧
      IsPat (N.displayedCluster c (N.graph.target g)) a b d e then θ.length g else 0)
    (fun g _ => by
      split_ifs
      · exact hw.1 g
      · exact le_rfl) (Finset.mem_univ f)
  unfold patWeight
  simpa [hf, hp] using this

omit [Fintype V] [Fintype E] [Nonempty X] in
/-- The alternatives of `ab|cd` are `ac|bd` and `ad|bc`. -/
theorem alternatives_quartetTree {a b d e : X} (h : ({a, b, d, e} : Finset X).card = 4)
    (h₁ : ({a, d, b, e} : Finset X).card = 4) (h₂ : ({a, e, b, d} : Finset X).card = 4) :
    (quartetTree a b d e h).alternatives = {quartetTree a d b e h₁, quartetTree a e b d h₂} := by
  obtain ⟨hab, had, hae, hbd, hbe, hde⟩ := ne_of_card_four h
  have ht₁ : ({a, d, b, e} : Finset X) = {a, b, d, e} := by
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  have ht₂ : ({a, e, b, d} : Finset X) = {a, b, d, e} := by
    ext x
    simp only [mem_insert, mem_singleton]
    tauto
  have hmem : ∀ {u v w z : X}, ({u, v} : Finset X) ∈ ({{w, z}, {u, v}} : Finset (Finset X)) := by
    intro u v w z
    simp
  have hne₁ : quartetTree a d b e h₁ ≠ quartetTree a b d e h := by
    intro he
    have hm : ({a, d} : Finset X) ∈ (quartetTree a b d e h).val := by rw [← he]; simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · have : d ∈ ({a, b} : Finset X) := hm ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact had h'.symm
      · exact hbd h'.symm
    · have : a ∈ ({d, e} : Finset X) := hm ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact had h'
      · exact hae h'
  have hne₂ : quartetTree a e b d h₂ ≠ quartetTree a b d e h := by
    intro he
    have hm : ({a, e} : Finset X) ∈ (quartetTree a b d e h).val := by rw [← he]; simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · have : e ∈ ({a, b} : Finset X) := hm ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact hae h'.symm
      · exact hbe h'.symm
    · have : a ∈ ({d, e} : Finset X) := hm ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact had h'
      · exact hae h'
  have hne : quartetTree a d b e h₁ ≠ quartetTree a e b d h₂ := by
    intro he
    have hm : ({a, d} : Finset X) ∈ (quartetTree a e b d h₂).val := by rw [← he]; simp
    simp only [quartetTree_val, mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · have : d ∈ ({a, e} : Finset X) := hm ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact had h'.symm
      · exact hde h'
    · have : a ∈ ({b, d} : Finset X) := hm ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact hab h'
      · exact had h'
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact QuartetTree.mem_alternatives.2 ⟨by
        rw [FalseEdge.taxa_quartetTree, FalseEdge.taxa_quartetTree, ht₁], hne₁⟩
    · exact QuartetTree.mem_alternatives.2 ⟨by
        rw [FalseEdge.taxa_quartetTree, FalseEdge.taxa_quartetTree, ht₂], hne₂⟩
  · rw [(quartetTree a b d e h).card_alternatives, Finset.card_pair hne]

/-- (`ext:rhodes2025_prop6_1`) **The analogue of Assumption 1 in the forward direction, for the displayed tree model, on any network.** A trivial 4-blob
gives equal sums of pairs, and a cut split gives `SP_ab|cd < SP_ac|bd = SP_ad|bc`: this is Proposition 6.1 of Rhodes et al. 2025,
item 1, by its argument: the sums of pairs are a mixture over the displayed trees. -/
theorem spForward_averageDist (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) :
    SPForward N (averageDist N θ) := by
  have hs := averageDist_comm (N := N) (θ := θ)
  have h0 := averageDist_self (N := N) (θ := θ)
  have hSP : ∀ {a b d e : X} (h : ({a, b, d, e} : Finset X).card = 4),
      spOf (averageDist N θ) (quartetTree a b d e h) = averageDist N θ a b + averageDist N θ d e :=
    fun h => spOf_quartetTree hs h0 h
  have hthree : ∀ {a b d e : X} (h : ({a, b, d, e} : Finset X).card = 4)
      (h₁ : ({a, d, b, e} : Finset X).card = 4) (h₂ : ({a, e, b, d} : Finset X).card = 4)
      (W : avgWeight N θ a d b e = 0) (W' : avgWeight N θ a e b d = 0),
      spOf (averageDist N θ) (quartetTree a d b e h₁) - spOf (averageDist N θ) (quartetTree a b d e h) =
        2 * avgWeight N θ a b d e ∧
      spOf (averageDist N θ) (quartetTree a e b d h₂) - spOf (averageDist N θ) (quartetTree a b d e h) =
        2 * avgWeight N θ a b d e := by
    intro a b d e h h₁ h₂ W W'
    have i₁ := sumOfPairs_sub_eq (N := N) (θ := θ) a b d e
    have i₂ := sumOfPairs_sub_eq (N := N) (θ := θ) a b e d
    rw [avgWeight_comm_right a b e d, W'] at i₂
    rw [W] at i₁
    rw [hSP h, hSP h₁, hSP h₂]
    constructor
    · linarith
    · have := hs e d
      linarith
  refine ⟨fun q hq ht r hr r' hr' => ?_, fun s hcut => ?_⟩
  · -- a trivial 4-blob: no displayed tree resolves it
    obtain ⟨a, b, d, e, h, rfl⟩ := TreeMetric.exists_eq_quartetTree r
    have hq' : q = {a, b, d, e} := by
      rw [← mem_treesOn.1 hr, FalseEdge.taxa_quartetTree]
    subst hq'
    have hzero : ∀ {u v w z : X} (hc : ({u, v, w, z} : Finset X).card = 4),
        ({u, v, w, z} : Finset X) = {a, b, d, e} → avgWeight N θ u v w z = 0 := by
      intro u v w z hc he
      refine Finset.sum_eq_zero fun c _ => ?_
      have : patWeight N θ c u v w z = 0 := Finset.sum_eq_zero fun f _ => ite_eq_right fun hp =>
        absurd (displays_of_isPat hc hp.2) (not_displays_of_hasTrivialFourBlob hN c hq ht
          (mem_treesOn.2 (by rw [FalseEdge.taxa_quartetTree, he])))
      rw [this, mul_zero]
    obtain ⟨hab, had, hae, hbd, hbe, hde⟩ := ne_of_card_four h
    have h₁ : ({a, d, b, e} : Finset X).card = 4 := TreeMetric.card_four_of_ne had hab hae hbd.symm hde hbe
    have h₂ : ({a, e, b, d} : Finset X).card = 4 := TreeMetric.card_four_of_ne hae hab had hbe.symm hde.symm hbd
    have ht₁ : ({a, d, b, e} : Finset X) = {a, b, d, e} := by
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
    have ht₂ : ({a, e, b, d} : Finset X) = {a, b, d, e} := by
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
    obtain ⟨hd₁, hd₂⟩ := hthree h h₁ h₂ (hzero h₁ ht₁) (hzero h₂ ht₂)
    rw [hzero h rfl, mul_zero] at hd₁ hd₂
    have hval : ∀ t ∈ treesOn ({a, b, d, e} : Finset X),
        spOf (averageDist N θ) t = spOf (averageDist N θ) (quartetTree a b d e h) := by
      intro t ht'
      by_cases hts : t = quartetTree a b d e h
      · rw [hts]
      · have halt : t ∈ (quartetTree a b d e h).alternatives :=
          QuartetTree.mem_alternatives.2 ⟨by
            rw [mem_treesOn.1 ht', FalseEdge.taxa_quartetTree], hts⟩
        rw [alternatives_quartetTree h h₁ h₂] at halt
        simp only [mem_insert, mem_singleton] at halt
        rcases halt with rfl | rfl <;> linarith
    rw [hval _ hr, hval _ hr']
  · -- a cut split: every displayed tree displays it
    obtain ⟨a, b, d, e, h, rfl⟩ := TreeMetric.exists_eq_quartetTree s
    obtain ⟨hab, had, hae, hbd, hbe, hde⟩ := ne_of_card_four h
    have h₁ : ({a, d, b, e} : Finset X).card = 4 := TreeMetric.card_four_of_ne had hab hae hbd.symm hde hbe
    have h₂ : ({a, e, b, d} : Finset X).card = 4 := TreeMetric.card_four_of_ne hae hab had hbe.symm hde.symm hbd
    have ht₁ : ({a, d, b, e} : Finset X) = {a, b, d, e} := by
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
    have ht₂ : ({a, e, b, d} : Finset X) = {a, b, d, e} := by
      ext x
      simp only [mem_insert, mem_singleton]
      tauto
    have hdisp := fun c : N.ParentChoice => displays_displayedSides_of_inducedCutSplit hN c hcut
    have halt := alternatives_quartetTree h h₁ h₂
    have hne₁ : quartetTree a d b e h₁ ≠ quartetTree a b d e h := fun he => by
      have hm : quartetTree a d b e h₁ ∈ (quartetTree a b d e h).alternatives := by rw [halt]; simp
      exact (QuartetTree.mem_alternatives.1 hm).2 he
    have hne₂ : quartetTree a e b d h₂ ≠ quartetTree a b d e h := fun he => by
      have hm : quartetTree a e b d h₂ ∈ (quartetTree a b d e h).alternatives := by rw [halt]; simp
      exact (QuartetTree.mem_alternatives.1 hm).2 he
    have hW₁ : avgWeight N θ a d b e = 0 := Finset.sum_eq_zero fun c _ => by
      rw [patWeight_eq_zero hN h₁ (hdisp c) (by rw [FalseEdge.taxa_quartetTree, ht₁]) hne₁, mul_zero]
    have hW₂ : avgWeight N θ a e b d = 0 := Finset.sum_eq_zero fun c _ => by
      rw [patWeight_eq_zero hN h₂ (hdisp c) (by rw [FalseEdge.taxa_quartetTree, ht₂]) hne₂, mul_zero]
    obtain ⟨hd₁, hd₂⟩ := hthree h h₁ h₂ hW₁ hW₂
    -- the separating arc, of positive length
    have hpos : 0 < avgWeight N θ a b d e := by
      obtain ⟨P, hP, f, hdom, hbelow⟩ := exists_separating_arc hN hcut
      obtain ⟨x, hx⟩ : P.Nonempty := Finset.card_pos.1 (by rw [(quartetTree a b d e h).card_of_mem hP]; omega)
      have hnh : ¬ N.IsHybridArc f := Remarks.not_isHybridArc_of_dominates hN (hdom x hx)
      have htree : N.IsTreeArc f := by
        have h₃ := hN.nonroot_indegree _ (target_ne_root_of_isPhylogenetic hN f)
        unfold RootedNetwork.IsHybridArc at hnh
        unfold RootedNetwork.IsTreeArc
        omega
      have hl := hθ.1 f htree
      have hne : Nonempty N.ParentChoice := by
        by_contra hcon
        have hemp : IsEmpty N.ParentChoice := not_nonempty_iff.1 hcon
        have hone := sum_choiceWeight hN hθ.isWeakMetric.isNormalized
        simp at hone
      obtain ⟨c⟩ := hne
      have hkept : f ∉ N.deletedArcs c :=
        ((hdom x hx).dominatesOff.isBelowOff hN (isDeletion_deletedArcs hN c)).1
      refine avgWeight_pos hθ c hkept ?_ hl
      simp only [quartetTree_val, mem_insert, mem_singleton] at hP
      have hin : ∀ y, N.Dominates f y → y ∈ N.displayedCluster c (N.graph.target f) := fun y hy =>
        mem_displayedCluster_of_dominates hN c hy
      have hout : ∀ y, ¬ N.IsBelow f y → y ∉ N.displayedCluster c (N.graph.target f) := fun y hy =>
        notMem_displayedCluster_of_not_isBelow hy
      rw [FalseEdge.taxa_quartetTree] at hbelow
      rcases hP with rfl | rfl
      · exact Or.inl ⟨hin _ (hdom a (by simp)), hin _ (hdom b (by simp)),
          hout _ (hbelow d (by simp) (by simp [had.symm, hbd.symm])),
          hout _ (hbelow e (by simp) (by simp [hae.symm, hbe.symm]))⟩
      · exact Or.inr ⟨hin _ (hdom d (by simp)), hin _ (hdom e (by simp)),
          hout _ (hbelow a (by simp) (by simp [had, hae])),
          hout _ (hbelow b (by simp) (by simp [hbd, hbe]))⟩
    refine ⟨fun r hr => ?_, fun r hr r' hr' => ?_⟩
    · rw [halt] at hr
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with rfl | rfl <;> linarith
    · rw [halt] at hr hr'
      simp only [mem_insert, mem_singleton] at hr hr'
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;> linarith

/-- (`ecto:sec10_sp_average`) **The framework on average distances, for the displayed tree model.** A sample of `n` displayed trees, with its path lengths,
under the analogue of Assumption 1: the output on the p-values `spStarP` and `spT1P`, with Bon or BBC, is the tree of blobs with
probability tending to one, at any levels with `o(n)` cutoffs. The forward direction holds at all valid parameters
(`spForward_averageDist`). -/
theorem consistency_averageDist (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hC : SPConverse N (averageDist N θ)) {T₀ : Finset (Finset X)}
    (hT₀ : IsResolutionOf T₀ (treeOfBlobs N)) {o : ECToBlobOptions}
    (hm : o.testCo = .bon ∨ o.testCo = .bbc) {α β : ℕ → ℝ} (hα₀ : Tendsto α atTop (𝓝[>] 0))
    (hβ₀ : Tendsto β atTop (𝓝[>] 0)) (hα : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 0))
    (hβ : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 0)) :
    Tendsto (fun n => iidProb (N.choiceWeight θ) n fun ω =>
      ectoblobBy o (α n) (β n)
        (fun s => spStarP (8 * (∑ f, |θ.length f| + 1)) (displayedDist N θ) s n ω)
        (fun s => spT1P (8 * (∑ f, |θ.length f| + 1)) (displayedDist N θ) s n ω) T₀ =
        treeOfBlobs N) atTop (𝓝 1) := by
  have hd : IsDist (N.choiceWeight θ) :=
    ⟨choiceWeight_nonneg hθ.isWeakMetric, sum_choiceWeight hN hθ.isWeakMetric.isNormalized⟩
  have hB : 0 < ∑ f, |θ.length f| + 1 := by
    have : 0 ≤ ∑ f, |θ.length f| := Finset.sum_nonneg fun f _ => abs_nonneg _
    linarith
  refine consistency_sumOfPairs hN hd hB (fun c x y => ?_) (spForward_averageDist hN hθ) hC hT₀ hm
    hα₀ hβ₀ hα hβ
  unfold displayedDist
  calc |∑ f, if f ∉ N.deletedArcs c then θ.length f * arcSep (N.displayedCluster c (N.graph.target f)) x y else 0|
      ≤ ∑ f, |if f ∉ N.deletedArcs c then θ.length f * arcSep (N.displayedCluster c (N.graph.target f)) x y else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f, |θ.length f| := Finset.sum_le_sum fun f _ => by
        by_cases hk : f ∉ N.deletedArcs c
        · rw [ite_eq_left hk, abs_mul]
          have : |arcSep (N.displayedCluster c (N.graph.target f)) x y| ≤ 1 := by
            unfold arcSep
            split_ifs <;> simp
          nlinarith [abs_nonneg (θ.length f)]
        · rw [ite_eq_right hk]
          simp
    _ ≤ _ := by linarith

end Average

/-! ### An instance of the converse -/

namespace Instance

open FinNetwork FinNetwork.Binary

/-- The cluster of `u` under a parent choice that keeps `u → h`. -/
theorem isPat_of_uh {c : net.ParentChoice} (huh : (7 : Fin 11) ∉ net.deletedArcs c) {x : Fin 5}
    (hx : x = 3 ∨ x = 4) : IsPat (net.displayedCluster c 6) 0 2 1 x := by
  have h₆ : (6 : Fin 11) ∉ net.deletedArcs c := notMem_deletedArcs_of_unique c (by decide) (by decide)
  have h₁₀ : (10 : Fin 11) ∉ net.deletedArcs c := notMem_deletedArcs_of_unique c (by decide) (by decide)
  have hout : ∀ y : Fin 5, lf y ∉ desc 6 → y ∉ net.displayedCluster c 6 := fun y hy hm =>
    hy (tables.reaches_iff.1 (mem_displayedCluster.1 hm).reaches)
  refine Or.inl ⟨mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨6, h₆, rfl, rfl⟩),
    mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨7, huh, rfl, rfl⟩
      (Relation.ReflTransGen.single ⟨10, h₁₀, rfl, rfl⟩)), hout 1 (by decide), hout x ?_⟩
  rcases hx with rfl | rfl <;> decide

/-- The cluster of `v` under a parent choice that keeps `v → h`. -/
theorem isPat_of_vh {c : net.ParentChoice} (hvh : (9 : Fin 11) ∉ net.deletedArcs c) {x : Fin 5}
    (hx : x = 3 ∨ x = 4) : IsPat (net.displayedCluster c 7) 1 2 0 x := by
  have h₈ : (8 : Fin 11) ∉ net.deletedArcs c := notMem_deletedArcs_of_unique c (by decide) (by decide)
  have h₁₀ : (10 : Fin 11) ∉ net.deletedArcs c := notMem_deletedArcs_of_unique c (by decide) (by decide)
  have hout : ∀ y : Fin 5, lf y ∉ desc 7 → y ∉ net.displayedCluster c 7 := fun y hy hm =>
    hy (tables.reaches_iff.1 (mem_displayedCluster.1 hm).reaches)
  refine Or.inl ⟨mem_displayedCluster.2 (Relation.ReflTransGen.single ⟨8, h₈, rfl, rfl⟩),
    mem_displayedCluster.2 (Relation.ReflTransGen.head ⟨9, hvh, rfl, rfl⟩
      (Relation.ReflTransGen.single ⟨10, h₁₀, rfl, rfl⟩)), hout 0 (by decide), hout x ?_⟩
  rcases hx with rfl | rfl <;> decide

/-- An arc dominating a taxon has positive length, at valid parameters. -/
theorem length_pos_of_dominates {θ : MetricData (Fin 11)} (hθ : net.IsMetric θ) {f : Fin 11} {y : Fin 5}
    (h : net.Dominates f y) : 0 < θ.length f := by
  have hN := net_isPhylogenetic
  have hnh : ¬ net.IsHybridArc f := Remarks.not_isHybridArc_of_dominates hN h
  have h₃ := hN.nonroot_indegree _ (target_ne_root_of_isPhylogenetic hN f)
  refine hθ.1 f ?_
  unfold RootedNetwork.IsHybridArc at hnh
  unfold RootedNetwork.IsTreeArc
  omega

/-- **The converse of the analogue of Assumption 1 on the binary network of `FinNetwork.Binary`**, at all valid parameters: on the
two sets of four taxa with no cut split, the sum of pairs of the quartet tree that no tree displays is strictly the largest. So
the framework applies to it (`consistency_averageDist`). -/
theorem spConverse_averageDist {θ : MetricData (Fin 11)} (hθ : net.IsMetric θ) :
    SPConverse net (averageDist net θ) := by
  have hN := net_isPhylogenetic
  have hF := spForward_averageDist hN hθ
  have hs := averageDist_comm (N := net) (θ := θ)
  have h0 := averageDist_self (N := net) (θ := θ)
  refine spConverse_of_cases hF fun q hq => ?_
  have hcases : ∀ q : Finset (Fin 5), q.card = 4 →
      (∃ y z : Fin 5, q = {3, 4, y, z} ∧ RDomT tgt lf desc avoid 3 4 y z) ∨
        ∃ x : Fin 5, (x = 3 ∨ x = 4) ∧ q = {0, 1, 2, x} := by decide
  rcases hcases q hq with ⟨y, z, rfl, hr⟩ | ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inl ⟨quartetTree 3 4 y z hq, by simp [treesOn],
      inducedCutSplit_of_rdom hN hq (tables.rdom_iff.2 hr)⟩)
  · right; right
    have h₁' : ({0, 2, 1, x} : Finset (Fin 5)).card = 4 := by
      rcases hx with rfl | rfl <;> decide
    have h₂' : ({1, 2, 0, x} : Finset (Fin 5)).card = 4 := by
      rcases hx with rfl | rfl <;> decide
    have ht₁ : ({0, 2, 1, x} : Finset (Fin 5)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have ht₂ : ({1, 2, 0, x} : Finset (Fin 5)) = {0, 1, 2, x} := by
      rcases hx with rfl | rfl <;> decide
    have hm₁ : quartetTree 0 2 1 x h₁' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [FalseEdge.taxa_quartetTree, ht₁]
    have hm₂ : quartetTree 1 2 0 x h₂' ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [FalseEdge.taxa_quartetTree, ht₂]
    have hm₃ : quartetTree 0 1 2 x hq ∈ treesOn ({0, 1, 2, x} : Finset (Fin 5)) := by
      simp only [treesOn, mem_filter, mem_univ, true_and]
      rw [FalseEdge.taxa_quartetTree]
    have h12 : quartetTree 0 2 1 x h₁' ≠ quartetTree 1 2 0 x h₂' := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    have h13 : quartetTree 0 2 1 x h₁' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    have h23 : quartetTree 1 2 0 x h₂' ≠ quartetTree 0 1 2 x hq := by
      intro h
      have := congrArg Subtype.val h
      simp only [quartetTree_val] at this
      rcases hx with rfl | rfl <;> exact absurd this (by decide)
    -- the weights
    have hW₃ : avgWeight net θ 0 1 2 x = 0 := Finset.sum_eq_zero fun c _ => by
      rcases uh_or_vh c with h | h
      · rw [patWeight_eq_zero hN hq (displays_of_uh h hx h₁')
          (by rw [FalseEdge.taxa_quartetTree, ht₁]) h13.symm, mul_zero]
      · rw [patWeight_eq_zero hN hq (displays_of_vh h hx h₂')
          (by rw [FalseEdge.taxa_quartetTree, ht₂]) h23.symm, mul_zero]
    have hW₁ : 0 < avgWeight net θ 0 2 1 x :=
      avgWeight_pos hθ choiceU (f := 4)
        (notMem_deletedArcs_of_unique choiceU (by decide) (by decide))
        (isPat_of_uh choiceU_keeps hx)
        (length_pos_of_dominates hθ (y := 0) (tables.dominates_iff.2 (by decide)))
    have hW₂ : 0 < avgWeight net θ 1 2 0 x :=
      avgWeight_pos hθ choiceV (f := 5)
        (notMem_deletedArcs_of_unique choiceV (by decide) (by decide))
        (isPat_of_vh choiceV_keeps hx)
        (length_pos_of_dominates hθ (y := 1) (tables.dominates_iff.2 (by decide)))
    have i₁ := sumOfPairs_sub_eq (N := net) (θ := θ) 0 2 1 x
    have i₂ := sumOfPairs_sub_eq (N := net) (θ := θ) 1 2 0 x
    rw [avgWeight_comm_left 1 0 2 x, hW₃] at i₂
    rw [hW₃] at i₁
    have hsym := hs 1 0
    refine ⟨_, hm₁, _, hm₂, _, hm₃, h12, h13, h23, ?_, ?_⟩
    · rw [spOf_quartetTree hs h0, spOf_quartetTree hs h0]
      simp only [FourPoint.sumOfPairs]
      linarith
    · rw [spOf_quartetTree hs h0, spOf_quartetTree hs h0]
      simp only [FourPoint.sumOfPairs]
      linarith

end Instance

end ECToBlob.SumOfPairs
