module

public import Basic.Testing.Defs
public import Basic.Testing.IID
public import Basic.Testing.Tails

/-!
# Gene trees with missing taxa

Two of the papers allow gene trees on subsets of the taxa. TINNiK, after its algorithm: "The TINNiK algorithm can also be applied when
gene trees have missing taxa, provided each subset of 4 taxa occurs on at least one gene tree, so the qcCF is not the zero vector", and
before its Theorem 4: "we also restrict to the case that the data is `m` gene trees, each on the full taxon set `X`, since generalizing from
this is straightforward". NANUQ, its Step 1: "If all four taxa are not on a gene tree, that tree does not contribute to the counts". This
file has what is common to both.

* `partialCount`: the counts of the printed Step 1, on gene trees given with their taxa. `quartetCountOn`: the same on sample-level
  gene trees `sides (ω i)` with the taxa `on i` kept, which is `partialCount` of the restrictions (`partialCount_restrict`).
* `sum_quartetCountOn_treesOn`, `quartetCountOn_treesOn_eq_zero_iff`: on gene trees that resolve what they contain, the qcCF of a set of
  four taxa is the zero vector exactly when the set occurs on no gene tree.

Under the model of the consistency theorems, the gene trees are independent, and the taxa kept are fixed in advance; they may depend on the
sample size. On a set `q`, the qcCF is that of the `coverCount on q` gene trees containing `q`, and these are independent draws
(`iidProb_quartetCountOn`). So the limits of the tests on `q` for samples of size `n` become limits along `coverCount on q`
(`tendsto_iidProb_on`, `tendsto_iidProb_on_level`).
-/

@[expose] public noncomputable section

open Finset Filter Topology
open scoped Classical

namespace Phylogenetics

variable {Γ : Type*} [Fintype Γ] {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The counts -/

/-- **Step 1 on gene trees with missing taxa**: on the `i`-th gene tree, with taxa `(data i).1` and sides of splits `(data i).2`, the quartet tree `s` is
counted when its taxa are all on the gene tree, and the gene tree displays it. "If all four taxa are not on a gene tree, that tree does
not contribute to the counts" (NANUQ). -/
def partialCount {n : ℕ} (data : Fin n → Finset X × Finset (Finset X)) (s : QuartetTree X) : ℝ :=
  ((univ.filter fun i => s.taxa ⊆ (data i).1 ∧ Displays (data i).2 s).card : ℝ)

/-- The number of the gene trees `ω` that have all the taxa of the quartet tree `s`, the `i`-th gene tree having the taxa `on i`, and display
`s`. -/
def quartetCountOn {n : ℕ} (sides : Γ → Finset (Finset X)) (on : Fin n → Finset X) (ω : Fin n → Γ)
    (s : QuartetTree X) : ℝ :=
  ((univ.filter fun i => s.taxa ⊆ on i ∧ Displays (sides (ω i)) s).card : ℝ)

/-- The tree induced on the taxa `S` by a tree with sides `T`. -/
def restrictSides (S : Finset X) (T : Finset (Finset X)) : Finset (Finset X) := T.image (· ∩ S)

omit [Fintype X] in
/-- The tree induced on `S` displays a quartet tree on taxa of `S` exactly when the tree does. -/
theorem displays_restrictSides {S : Finset X} {T : Finset (Finset X)} {s : QuartetTree X} (hs : s.taxa ⊆ S) :
    Displays (restrictSides S T) s ↔ Displays T s := by
  have key : ∀ A : Finset X, A ∩ S ∩ s.taxa = A ∩ s.taxa := fun A => by
    rw [inter_assoc, inter_eq_right.2 hs]
  constructor
  · rintro ⟨A', hA', hd⟩
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    exact ⟨A, hA, by rwa [key] at hd⟩
  · rintro ⟨A, hA, hd⟩
    exact ⟨A ∩ S, mem_image.2 ⟨A, hA, rfl⟩, by rwa [key]⟩

omit [Fintype Γ] [Fintype X] in
/-- `quartetCountOn` is Step 1 on the gene trees induced on the taxa kept. Under the network multispecies coalescent, a gene tree on a subset of
the taxa is such a tree, by sampling consistency. -/
theorem partialCount_restrict {n : ℕ} (sides : Γ → Finset (Finset X)) (on : Fin n → Finset X) (ω : Fin n → Γ) :
    partialCount (fun i => (on i, restrictSides (on i) (sides (ω i)))) = quartetCountOn sides on ω := by
  funext s
  simp only [partialCount, quartetCountOn]
  congr 2
  refine filter_congr fun i _ => and_congr_right fun hs => displays_restrictSides hs

omit [Fintype Γ] [Fintype X] in
theorem quartetCountOn_nonneg {n : ℕ} (sides : Γ → Finset (Finset X)) (on : Fin n → Finset X) (ω : Fin n → Γ)
    (s : QuartetTree X) : 0 ≤ quartetCountOn sides on ω s :=
  Nat.cast_nonneg _

/-- The gene trees containing the taxa `q`. -/
def coverIndices {n : ℕ} (on : Fin n → Finset X) (q : Finset X) : Finset (Fin n) := univ.filter fun i => q ⊆ on i

/-- **How many gene trees contain the taxa `q`.** -/
def coverCount {n : ℕ} (on : Fin n → Finset X) (q : Finset X) : ℕ := (coverIndices on q).card

/-- The gene trees containing the taxa `q`, listed. -/
def coverEmb {n : ℕ} (on : Fin n → Finset X) (q : Finset X) : Fin (coverCount on q) ↪ Fin n :=
  ((coverIndices on q).orderEmbOfFin rfl).toEmbedding

omit [Fintype X] in
theorem mem_coverIndices {n : ℕ} {on : Fin n → Finset X} {q : Finset X} {i : Fin n} :
    i ∈ coverIndices on q ↔ q ⊆ on i := by
  simp [coverIndices]

omit [Fintype X] in
theorem coverEmb_mem {n : ℕ} (on : Fin n → Finset X) (q : Finset X) (j : Fin (coverCount on q)) :
    q ⊆ on (coverEmb on q j) :=
  mem_coverIndices.1 (Finset.orderEmbOfFin_mem _ rfl j)

omit [Fintype X] in
theorem exists_coverEmb_eq {n : ℕ} {on : Fin n → Finset X} {q : Finset X} {i : Fin n} (hi : q ⊆ on i) :
    ∃ j, coverEmb on q j = i := by
  have h : i ∈ Set.range ((coverIndices on q).orderEmbOfFin (rfl : (coverIndices on q).card = coverCount on q)) := by
    rw [Finset.range_orderEmbOfFin]
    exact mem_coe.2 (mem_coverIndices.2 hi)
  exact h

omit [Fintype Γ] in
/-- **On the taxa `q`, the counts are those of the gene trees containing `q`.** -/
theorem quartetCountOn_eq {n : ℕ} (sides : Γ → Finset (Finset X)) (on : Fin n → Finset X) (ω : Fin n → Γ)
    {q : Finset X} {s : QuartetTree X} (hs : s ∈ treesOn q) :
    quartetCountOn sides on ω s = quartetCount sides (ω ∘ coverEmb on q) s := by
  have hst : s.taxa = q := mem_treesOn.1 hs
  simp only [quartetCountOn, quartetCount, hst]
  congr 1
  refine (card_bij (fun j _ => coverEmb on q j) ?_ ?_ ?_).symm
  · intro j hj
    exact mem_filter.2 ⟨mem_univ _, coverEmb_mem on q j, (mem_filter.1 hj).2⟩
  · intro j _ j' _ h
    exact (coverEmb on q).injective h
  · intro i hi
    obtain ⟨-, hi₁, hi₂⟩ := mem_filter.1 hi
    obtain ⟨j, rfl⟩ := exists_coverEmb_eq hi₁
    exact ⟨j, mem_filter.2 ⟨mem_univ _, hi₂⟩, rfl⟩

omit [Fintype Γ] in
/-- **The total of a qcCF** on gene trees that resolve the taxa `q` when they contain them: the number of gene trees containing `q`. -/
theorem sum_quartetCountOn_treesOn {n : ℕ} {sides : Γ → Finset (Finset X)} {on : Fin n → Finset X} {ω : Fin n → Γ}
    {q : Finset X} (hone : ∀ i, q ⊆ on i → ∃! s, s ∈ treesOn q ∧ Displays (sides (ω i)) s) :
    ∑ r ∈ treesOn q, quartetCountOn sides on ω r = coverCount on q := by
  have hsum : ∀ i : Fin n, (∑ r ∈ treesOn q, if r.taxa ⊆ on i ∧ Displays (sides (ω i)) r then (1 : ℝ) else 0) =
      if q ⊆ on i then 1 else 0 := by
    intro i
    by_cases hi : q ⊆ on i
    · obtain ⟨s, ⟨hs, hd⟩, huniq⟩ := hone i hi
      rw [ite_eq_left hi, sum_eq_single_of_mem s hs]
      · rw [ite_eq_left ⟨(mem_treesOn.1 hs).symm ▸ hi, hd⟩]
      · intro r hr hrs
        exact ite_eq_right fun h => hrs (huniq r ⟨hr, h.2⟩)
    · rw [ite_eq_right hi]
      refine sum_eq_zero fun r hr => ?_
      exact ite_eq_right fun h => hi ((mem_treesOn.1 hr) ▸ h.1)
  simp only [quartetCountOn, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, coverCount, coverIndices]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => hsum i

omit [Fintype Γ] in
/-- **"Provided each subset of 4 taxa occurs on at least one gene tree, so the qcCF is not the zero vector"** (TINNiK, after its algorithm), on
gene trees that resolve the taxa they contain: the qcCF is the zero vector exactly when the taxa `q` occur on no gene tree. -/
theorem quartetCountOn_treesOn_eq_zero_iff {n : ℕ} {sides : Γ → Finset (Finset X)} {on : Fin n → Finset X} {ω : Fin n → Γ}
    {q : Finset X} (hone : ∀ i, q ⊆ on i → ∃! s, s ∈ treesOn q ∧ Displays (sides (ω i)) s) :
    (∀ r ∈ treesOn q, quartetCountOn sides on ω r = 0) ↔ ∀ i, ¬ q ⊆ on i := by
  have hsum := sum_quartetCountOn_treesOn hone
  have hzero : (∀ r ∈ treesOn q, quartetCountOn sides on ω r = 0) ↔ coverCount on q = 0 := by
    rw [← Nat.cast_eq_zero (R := ℝ), ← hsum]
    exact (sum_eq_zero_iff_of_nonneg fun r _ => quartetCountOn_nonneg sides on ω r).symm
  rw [hzero, coverCount, card_eq_zero]
  constructor
  · intro h i hi
    exact notMem_empty i (h ▸ mem_coverIndices.2 hi)
  · intro h
    exact eq_empty_of_forall_notMem fun i hi => h i (mem_coverIndices.1 hi)

omit [Fintype Γ] in
/-- **"Normalizing so that the qCFs for `Y` sum to 1 if gene trees are missing taxa"** (TOB-QMC, embedded line 408): dividing by the number of gene trees containing the set. -/
theorem sum_quartetCountOn_div {n : ℕ} {sides : Γ → Finset (Finset X)} {on : Fin n → Finset X} {ω : Fin n → Γ}
    {q : Finset X} (hone : ∀ i, q ⊆ on i → ∃! s, s ∈ treesOn q ∧ Displays (sides (ω i)) s) (hq : coverCount on q ≠ 0) :
    ∑ r ∈ treesOn q, quartetCountOn sides on ω r / coverCount on q = 1 := by
  rw [← sum_div, sum_quartetCountOn_treesOn hone]
  exact div_self (Nat.cast_ne_zero.2 hq)

/-! ### Independent draws -/

variable {dist : Γ → ℝ}

/-- **Independent draws on a subset of the indices are independent draws.** -/
theorem iidProb_comp_embedding (hd : IsDist dist) {n k : ℕ} (e : Fin k ↪ Fin n) (E : (Fin k → Γ) → Prop) :
    iidProb dist n (fun ω => E (ω ∘ e)) = iidProb dist k E := by
  let p : Fin n → Prop := fun i => i ∈ Set.range e
  let eS : Fin k ≃ {i // p i} := Equiv.ofInjective e e.injective
  have hrest : ∑ b : ({i // ¬ p i} → Γ), ∏ i, dist (b i) = 1 := by
    have := Finset.prod_univ_sum (fun _ : {i // ¬ p i} => (univ : Finset Γ)) (fun _ g => dist g)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    simp [hd.2]
  have hsplit : ∀ (a : {i // p i} → Γ) (b : {i // ¬ p i} → Γ) (i : {i // p i}),
      (Equiv.piEquivPiSubtypeProd p (fun _ => Γ)).symm (a, b) i.val = a i := by
    intro a b i
    simp [Equiv.piEquivPiSubtypeProd, i.property]
  have hsplit' : ∀ (a : {i // p i} → Γ) (b : {i // ¬ p i} → Γ) (i : {i // ¬ p i}),
      (Equiv.piEquivPiSubtypeProd p (fun _ => Γ)).symm (a, b) i.val = b i := by
    intro a b i
    simp [Equiv.piEquivPiSubtypeProd, i.property]
  have hcomp : ∀ (a : {i // p i} → Γ) (b : {i // ¬ p i} → Γ),
      (Equiv.piEquivPiSubtypeProd p (fun _ => Γ)).symm (a, b) ∘ e = a ∘ eS := by
    intro a b
    funext j
    exact hsplit a b (eS j)
  unfold iidProb
  rw [← (Equiv.piEquivPiSubtypeProd p (fun _ => Γ)).symm.sum_comp, Fintype.sum_prod_type]
  rw [← (eS.arrowCongr (Equiv.refl Γ)).sum_comp]
  refine sum_congr rfl fun η _ => ?_
  set a : {i // p i} → Γ := eS.arrowCongr (Equiv.refl Γ) η with ha
  have haη : a ∘ eS = η := by
    funext j
    simp [ha, Equiv.arrowCongr]
  have hterm : ∀ b : ({i // ¬ p i} → Γ),
      (if E ((Equiv.piEquivPiSubtypeProd p (fun _ => Γ)).symm (a, b) ∘ e) then
          ∏ i, dist ((Equiv.piEquivPiSubtypeProd p (fun _ => Γ)).symm (a, b) i) else 0) =
        (if E η then ∏ j, dist (η j) else 0) * ∏ i, dist (b i) := by
    intro b
    rw [hcomp, haη]
    by_cases hE : E η
    · rw [ite_eq_left hE, ite_eq_left hE, ← Fintype.prod_subtype_mul_prod_subtype p]
      congr 1
      · refine Finset.prod_equiv eS.symm (by simp) fun i _ => ?_
        rw [hsplit a b i]
        simp [ha, Equiv.arrowCongr]
      · exact prod_congr rfl fun i _ => by rw [hsplit' a b i]
    · simp [hE]
  rw [sum_congr rfl fun b _ => hterm b, ← mul_sum, hrest, mul_one]

/-- An event on the counts that looks only at the taxa `q`. -/
def DependsOnTaxa (q : Finset X) (Ev : (QuartetTree X → ℝ) → Prop) : Prop :=
  ∀ c c' : QuartetTree X → ℝ, (∀ r ∈ treesOn q, c r = c' r) → (Ev c ↔ Ev c')

/-- **The law of the qcCF on the taxa `q`, with missing taxa, is that of a sample of the gene trees containing `q`.** -/
theorem iidProb_quartetCountOn (hd : IsDist dist) (sides : Γ → Finset (Finset X)) {q : Finset X} {n : ℕ}
    (on : Fin n → Finset X) {Ev : (QuartetTree X → ℝ) → Prop} (hEv : DependsOnTaxa q Ev) :
    iidProb dist n (fun ω => Ev (quartetCountOn sides on ω)) =
      iidProb dist (coverCount on q) fun η => Ev (quartetCount sides η) := by
  rw [← iidProb_comp_embedding hd (coverEmb on q)]
  unfold iidProb
  refine sum_congr rfl fun ω _ => ?_
  have h : Ev (quartetCountOn sides on ω) ↔ Ev (quartetCount sides (ω ∘ coverEmb on q)) :=
    hEv _ _ fun r hr => quartetCountOn_eq sides on ω hr
  simp only [h]

/-- **A limit of the tests transfers to missing taxa**, when the number of gene trees containing the taxa `q` grows. The taxa kept may depend
on the sample size. -/
theorem tendsto_iidProb_on (hd : IsDist dist) (sides : Γ → Finset (Finset X)) {q : Finset X}
    {on : (m : ℕ) → Fin m → Finset X} (hk : Tendsto (fun m => coverCount (on m) q) atTop atTop)
    {Ev : ℕ → (QuartetTree X → ℝ) → Prop} (hEv : ∀ n, DependsOnTaxa q (Ev n))
    (h : Tendsto (fun n => iidProb dist n fun η => Ev n (quartetCount sides η)) atTop (𝓝 1)) :
    Tendsto (fun m => iidProb dist m fun ω => Ev (coverCount (on m) q) (quartetCountOn sides (on m) ω)) atTop (𝓝 1) := by
  refine (h.comp hk).congr fun m => ?_
  simp only [Function.comp]
  exact (iidProb_quartetCountOn hd sides (on m) (hEv _)).symm

/-- `a n` is above the levels `α m` of the samples with `k m = n`, and it tends to zero. -/
theorem exists_level_reindex {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0)) (k : ℕ → ℕ) :
    ∃ a : ℕ → ℝ, Tendsto a atTop (𝓝 0) ∧ ∀ m, α m ≤ a (k m) := by
  have hbdd : BddAbove (Set.range fun m => |α m|) := by
    have := hα.abs
    exact this.bddAbove_range
  have hbdd' : ∀ n, BddAbove (Set.range fun m : {m // k m = n} => |α m.val|) := fun n =>
    hbdd.mono (by rintro _ ⟨m, rfl⟩; exact ⟨m.val, rfl⟩)
  refine ⟨fun n => ⨆ m : {m // k m = n}, |α m.val|, ?_, fun m => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hα (ε / 2) (half_pos hε)
    refine ⟨(range M).sup k + 1, fun n hn => ?_⟩
    have hnn : 0 ≤ ⨆ m : {m // k m = n}, |α m.val| := Real.iSup_nonneg fun _ => abs_nonneg _
    have hle : (⨆ m : {m // k m = n}, |α m.val|) ≤ ε / 2 := by
      refine Real.iSup_le (fun m => ?_) (half_pos hε).le
      have hmM : M ≤ m.val := by
        by_contra hlt
        have h1 : k m.val ≤ (range M).sup k := Finset.le_sup (mem_range.2 (not_le.1 hlt))
        have h2 := m.property
        omega
      have := hM m.val hmM
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  · exact (le_abs_self _).trans (le_ciSup (hbdd' (k m)) ⟨m, rfl⟩)

/-- **The limit of a test under its null, with levels tending to zero, transfers to missing taxa**, for levels indexed by the number of gene
trees, whatever the number of them that contain the taxa `q`, provided it grows. -/
theorem tendsto_iidProb_on_level (hd : IsDist dist) (sides : Γ → Finset (Finset X)) {q : Finset X}
    {on : (m : ℕ) → Fin m → Finset X} (hk : Tendsto (fun m => coverCount (on m) q) atTop atTop)
    {G : (QuartetTree X → ℝ) → Prop} {f : (QuartetTree X → ℝ) → ℝ} (hG : DependsOnTaxa q G)
    (hf : ∀ c c' : QuartetTree X → ℝ, (∀ r ∈ treesOn q, c r = c' r) → f c = f c')
    (h : ∀ a : ℕ → ℝ, Tendsto a atTop (𝓝 0) →
      Tendsto (fun n => iidProb dist n fun η => G (quartetCount sides η) ∧ a n ≤ f (quartetCount sides η)) atTop (𝓝 1))
    {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun m => iidProb dist m fun ω => G (quartetCountOn sides (on m) ω) ∧ α m ≤ f (quartetCountOn sides (on m) ω))
      atTop (𝓝 1) := by
  obtain ⟨a, ha₀, ha⟩ := exists_level_reindex hα fun m => coverCount (on m) q
  have hdep : ∀ n, DependsOnTaxa q fun c => G c ∧ a n ≤ f c := fun n c c' hcc =>
    and_congr (hG c c' hcc) (by rw [hf c c' hcc])
  refine tendsto_iidProb_of_imp hd (Eventually.of_forall fun m ω hω => ⟨hω.1, (ha m).trans hω.2⟩)
    (tendsto_iidProb_on hd sides hk hdep (h a ha₀))

/-! ### The statistics look only at the taxa -/

section Congr

variable {c c' : QuartetTree X → ℝ} {q : Finset X}

theorem lineStat_congr {s : QuartetTree X} (hs : s ∈ treesOn q) (h : ∀ r ∈ treesOn q, c r = c' r) :
    lineStat c s = lineStat c' s := by
  have halt : ∀ r ∈ s.alternatives, c r = c' r := fun r hr =>
    h r (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs)))
  unfold lineStat
  rw [sum_congr rfl fun r hr => by rw [halt r hr], sum_congr rfl halt]

theorem starStat_congr (h : ∀ r ∈ treesOn q, c r = c' r) : starStat c q = starStat c' q := by
  unfold starStat
  rw [sum_congr rfl fun r hr => by rw [h r hr], sum_congr rfl h]

theorem starPValue_lrt_congr (h : ∀ r ∈ treesOn q, c r = c' r) : starPValue .lrt c q = starPValue .lrt c' q := by
  simp only [starPValue, starStat_congr h]

theorem cutStat_congr (h : ∀ r ∈ treesOn q, c r = c' r) : cutStat c q = cutStat c' q := by
  unfold cutStat
  exact iInf_congr fun s => lineStat_congr s.property h

theorem cutPValue_congr {s : QuartetTree X} (hs : s ∈ treesOn q) (h : ∀ r ∈ treesOn q, c r = c' r) :
    cutPValue c s = cutPValue c' s := by
  have halt : ∀ r ∈ s.alternatives, c r = c' r := fun r hr =>
    h r (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs)))
  unfold cutPValue
  rw [sum_congr rfl halt, h s hs, mem_treesOn.1 hs, cutStat_congr h]

theorem t1Stat_congr {s : QuartetTree X} (hs : s ∈ treesOn q) (h : ∀ r ∈ treesOn q, c r = c' r) :
    t1Stat c s = t1Stat c' s := by
  have halt : ∀ r ∈ s.alternatives, c r = c' r := fun r hr =>
    h r (mem_treesOn.2 ((QuartetTree.mem_alternatives.1 hr).1.trans (mem_treesOn.1 hs)))
  unfold t1Stat
  rw [sum_congr rfl halt, h s hs, lineStat_congr hs h, mem_treesOn.1 hs, starStat_congr h]

end Congr

end Phylogenetics
