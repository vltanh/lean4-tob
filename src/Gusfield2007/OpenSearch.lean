module

public import Gusfield2007.LabelSearch
public import Gusfield2007.OpenStatements

/-!
# Gusfield et al. 2007: a verified search on two extra labels, and histories from lists

Two tools for `Gusfield2007.Theorem10PrintedMultiple`, on numbers as in `Gusfield2007.LabelSearch`. Neither is in the paper.

* `LabelSearch.lt_RS_of_check2`: a lower bound on `R_S(M)`, for `S` a row, when `M` has `m + b - 1` rows: a history with at most `b` recombinations has at most two labels off the rows. `LabelSearch.level1` goes through the labels
  that a history can reach next and that give a row, rather than through all sequences, so it applies with many sites.
* `LabelSearch.RS_le_of_run`: an upper bound on `R_S(M)`, from a list of the steps of a history.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace LabelSearch

/-! ### The labels that can come next -/

/-- All the numbers below `2 ^ k` each of whose bits is that of `p` or `p'`. -/
def sub (p p' : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | k + 1 =>
    bif Nat.testBit p k then
      bif Nat.testBit p' k then (sub p p' k).map (fun x => Nat.lor x (2 ^ k))
      else sub p p' k ++ (sub p p' k).map (fun x => Nat.lor x (2 ^ k))
    else
      bif Nat.testBit p' k then sub p p' k ++ (sub p p' k).map (fun x => Nat.lor x (2 ^ k))
      else sub p p' k

/-- The pairs of a list. -/
def pairsOf : List ℕ → List (ℕ × ℕ)
  | [] => []
  | p :: l => l.map (fun q => (p, q)) ++ pairsOf l

/-- Each of `a` is a mix of `b`. -/
def dominated (a b : ℕ × ℕ) : Bool := isMix a.1 b.1 b.2 && isMix a.2 b.1 b.2

/-- The pairs that aren't strictly dominated by another. -/
def maxPairs (P : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  P.filter fun a => !P.any fun b => dominated a b && !dominated b a

/-- Pairs such that each mix of a pair of `P` is a mix of one of them. -/
def coverPairs (P : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  maxPairs P ++ P.filter fun a => !(maxPairs P).any (dominated a)

/-- The sequences one step from `X`: with one site changed, or a mix of two. -/
def cands (m : ℕ) (X : List ℕ) : List ℕ :=
  X.flatMap (fun p => (List.range m).map fun i => Nat.xor p (2 ^ i)) ++
    (coverPairs (pairsOf X)).flatMap fun pq => sub pq.1 pq.2 m

/-- The masks of `Ds` that contain no other. -/
def minMasks (Ds : List ℕ) : List ℕ :=
  Ds.filter fun D => !Ds.any fun D' => !Nat.beq D' D && Nat.beq (Nat.land D' D) D'

/-- For each row, the masks on one of which a new sequence has to agree with the row, for the row to be a mix of it and of a sequence of `X`. -/
def table (rest X : List ℕ) : List (ℕ × List ℕ) :=
  rest.map fun r => (r, minMasks (X.map fun p => Nat.xor r p))

/-- The number is a power of two. -/
def oneBit (d : ℕ) : Bool := Nat.beq (Nat.land d (d - 1)) 0 && !Nat.beq d 0

/-- The list without repetitions, added to `acc`. -/
def dedupN (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | a :: l => bif memN a acc then dedupN acc l else dedupN (a :: acc) l

/-- The mixes of `u`, `v` that give a row in one step, with what the row `t` asks of them. -/
def progMix (T : List (ℕ × List ℕ)) (m : ℕ) (uv : ℕ × ℕ) : List ℕ :=
  T.flatMap fun t =>
    (bif oneBit (Nat.land (Nat.xor t.1 uv.1) (Nat.xor t.1 uv.2)) then [Nat.xor t.1 (Nat.land (Nat.xor t.1 uv.1) (Nat.xor t.1 uv.2))] else []) ++
      t.2.flatMap fun M =>
        bif Nat.beq (Nat.land (Nat.land (Nat.xor t.1 uv.1) (Nat.xor t.1 uv.2)) M) 0 then
          sub (Nat.xor uv.1 (Nat.land (Nat.xor t.1 uv.1) M)) (Nat.xor uv.2 (Nat.land (Nat.xor t.1 uv.2) M)) m
        else []

/-- The sequences one site from `x` that give a row in one step. -/
def progFlip (T : List (ℕ × List ℕ)) (x : ℕ) : List ℕ :=
  T.flatMap fun t =>
    (bif oneBit (Nat.xor (Nat.xor t.1 x) (2 ^ Nat.log2 (Nat.xor t.1 x))) then
      [Nat.xor x (2 ^ Nat.log2 (Nat.xor t.1 x)), Nat.xor x (Nat.xor (Nat.xor t.1 x) (2 ^ Nat.log2 (Nat.xor t.1 x)))] else []) ++
      t.2.flatMap fun M => bif oneBit (Nat.land (Nat.xor t.1 x) M) then [Nat.xor x (Nat.land (Nat.xor t.1 x) M)] else []

/-- The sequences one step from `X` that give a row in one step, with `X`. -/
def progAll (m : ℕ) (T : List (ℕ × List ℕ)) (W : List (ℕ × ℕ)) (X : List ℕ) : List ℕ :=
  dedupN [] (X.flatMap (progFlip T) ++ W.flatMap (progMix T m))

/-- `r` is one step from `N ++ X`, using a sequence of `N`. -/
def derivN (N X : List ℕ) (r : ℕ) : Bool :=
  N.any fun p => oneStep r p || (N ++ X).any fun p' => isMix r p p'

/-- What `N ++ X` generates inside `N ++ X ++ rest`, given what `X` generates; and the rows left. Out of fuel, it says that no row is left. -/
def clos : ℕ → List ℕ → List ℕ → List ℕ → List ℕ × List ℕ
  | 0, _, _, _ => ([], [])
  | f + 1, N, X, rest =>
    match rest.filter (derivN N X) with
    | [] => (N ++ X, rest)
    | new => clos f new (N ++ X) (rest.filter fun r => !derivN N X r)

/-- The second extra label `z2`, after `X1`: a row is still missing. -/
def level2 (fuel : ℕ) (X1 rest1 Mc : List ℕ) (z2 : ℕ) : Bool :=
  memN z2 Mc || memN z2 X1 || !(clos fuel [z2] X1 rest1).2.isEmpty

/-- After the first extra label. -/
def level1' (fuel m : ℕ) (Mc : List ℕ) (c : List ℕ × List ℕ) : Bool :=
  !c.2.isEmpty && (progAll m (table c.2 c.1) (coverPairs (pairsOf c.1)) c.1).all (level2 fuel c.1 c.2 Mc)

/-- The first extra label `z1`: from the rows `X0` that the root generates among the rows `Mc`, no second label gives all the rows. -/
def level1 (fuel m : ℕ) (X0 rest0 Mc : List ℕ) (z1 : ℕ) : Bool :=
  memN z1 Mc || memN z1 X0 || level1' fuel m Mc (clos fuel [z1] X0 rest0)

/-! ### Bits -/

theorem isMix_iff {q p p' : ℕ} : isMix q p p' = true ↔ ∀ i, q.testBit i = p.testBit i ∨ q.testBit i = p'.testBit i := by
  unfold isMix
  rw [Nat.beq_eq]
  constructor
  · intro h i
    have h' := congrArg (fun x => Nat.testBit x i) h
    change (((q ^^^ p) &&& (q ^^^ p')).testBit i) = Nat.testBit 0 i at h'
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.zero_testBit] at h'
    cases hq : q.testBit i <;> cases hp : p.testBit i <;> cases hp' : p'.testBit i <;> simp_all
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    change ((q ^^^ p) &&& (q ^^^ p')).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.zero_testBit]
    rcases h i with h' | h' <;> rw [h'] <;> simp

theorem isMix_comm (q p p' : ℕ) : isMix q p p' = isMix q p' p := by
  unfold isMix
  rw [show Nat.land (Nat.xor q p) (Nat.xor q p') = Nat.land (Nat.xor q p') (Nat.xor q p) from Nat.and_comm _ _]

theorem mem_sub {p p' : ℕ} : ∀ (k q : ℕ), q < 2 ^ k → (∀ i < k, q.testBit i = p.testBit i ∨ q.testBit i = p'.testBit i) → q ∈ sub p p' k := by
  intro k
  induction k with
  | zero =>
    intro q hq _
    have : q = 0 := by simpa using hq
    simp [sub, this]
  | succ k ih =>
    intro q hq h
    have hq' : q % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hbits : ∀ i, (q % 2 ^ k).testBit i = (decide (i < k) && q.testBit i) := fun i => Nat.testBit_mod_two_pow q k i
    have hsub : q % 2 ^ k ∈ sub p p' k := ih _ hq' fun i hi => by
      rw [hbits]
      simpa [hi] using h i (Nat.lt_succ_of_lt hi)
    have hhigh : ∀ j, k < j → q.testBit j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) hj))
    have hone : q.testBit k = true → q = Nat.lor (q % 2 ^ k) (2 ^ k) := fun hb => by
      apply Nat.eq_of_testBit_eq
      intro j
      change _ = ((q % 2 ^ k) ||| 2 ^ k).testBit j
      rw [Nat.testBit_or, hbits, Nat.testBit_two_pow]
      rcases lt_trichotomy j k with hj | rfl | hj
      · simp [hj, hj.ne']
      · simp [hb]
      · simp [hhigh j hj, hj.ne, not_lt.2 hj.le]
    have hzero : q.testBit k = false → q = q % 2 ^ k := fun hb => by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [hbits]
      rcases lt_trichotomy j k with hj | rfl | hj
      · simp [hj]
      · simp [hb]
      · simp [hhigh j hj, not_lt.2 hj.le]
    have hk := h k (Nat.lt_succ_self k)
    rw [sub]
    cases hp : p.testBit k <;> cases hp' : p'.testBit k <;> simp only [Bool.cond_true, Bool.cond_false]
    · have hb : q.testBit k = false := by
        rcases hk with hk | hk
        · rw [hk, hp]
        · rw [hk, hp']
      rw [hzero hb]
      exact hsub
    · cases hb : q.testBit k
      · rw [hzero hb]
        exact List.mem_append_left _ hsub
      · rw [hone hb]
        exact List.mem_append_right _ (List.mem_map_of_mem hsub)
    · cases hb : q.testBit k
      · rw [hzero hb]
        exact List.mem_append_left _ hsub
      · rw [hone hb]
        exact List.mem_append_right _ (List.mem_map_of_mem hsub)
    · have hb : q.testBit k = true := by
        rcases hk with hk | hk
        · rw [hk, hp]
        · rw [hk, hp']
      rw [hone hb]
      exact List.mem_map_of_mem hsub

theorem mem_pairsOf_of_ne {p p' : ℕ} : ∀ {X : List ℕ}, p ∈ X → p' ∈ X → p ≠ p' → (p, p') ∈ pairsOf X ∨ (p', p) ∈ pairsOf X := by
  intro X
  induction X with
  | nil => simp
  | cons a l ih =>
    intro hp hp' hne
    rw [pairsOf]
    rcases List.mem_cons.1 hp with rfl | hp₁ <;> rcases List.mem_cons.1 hp' with rfl | hp₂
    · exact absurd rfl hne
    · exact Or.inl (List.mem_append_left _ (List.mem_map_of_mem hp₂))
    · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem hp₁))
    · rcases ih hp₁ hp₂ hne with h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr (List.mem_append_right _ h)

theorem exists_coverPairs {P : List (ℕ × ℕ)} {a : ℕ × ℕ} (ha : a ∈ P) : ∃ b ∈ coverPairs P, a = b ∨ dominated a b = true := by
  by_cases h : (maxPairs P).any (dominated a) = true
  · obtain ⟨b, hb, hd⟩ := List.any_eq_true.1 h
    exact ⟨b, List.mem_append_left _ hb, Or.inr hd⟩
  · exact ⟨a, List.mem_append_right _ (List.mem_filter.2 ⟨ha, by simpa using h⟩), Or.inl rfl⟩

/-! ### Going one step further -/

theorem derivable_eq_true_iff {X : List ℕ} {r : ℕ} :
    derivable X r = true ↔ ∃ p ∈ X, oneStep r p = true ∨ ∃ p' ∈ X, isMix r p p' = true := by
  simp [derivable, List.any_eq_true]

theorem derivable_append_of_true {N X : List ℕ} {r : ℕ} (h : derivable (N ++ X) r = true) : derivable X r = true ∨ derivN N X r = true := by
  obtain ⟨p, hp, hd⟩ := derivable_eq_true_iff.1 h
  rcases List.mem_append.1 hp with hp | hp
  · right
    refine List.any_eq_true.2 ⟨p, hp, ?_⟩
    rcases hd with hd | ⟨p', hp', hd⟩
    · simp [hd]
    · simp only [Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.2 ⟨p', hp', hd⟩)
  · rcases hd with hd | ⟨p', hp', hd⟩
    · exact Or.inl (derivable_eq_true_iff.2 ⟨p, hp, Or.inl hd⟩)
    · rcases List.mem_append.1 hp' with hp' | hp'
      · right
        refine List.any_eq_true.2 ⟨p', hp', ?_⟩
        simp only [Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.2 ⟨p, List.mem_append_right _ hp, by rw [isMix_comm]; exact hd⟩)
      · exact Or.inl (derivable_eq_true_iff.2 ⟨p, hp, Or.inr ⟨p', hp', hd⟩⟩)

theorem exists_minMasks {Ds : List ℕ} : ∀ D ∈ Ds, ∃ M ∈ minMasks Ds, Nat.land M D = M := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro hD
    by_cases hmin : D ∈ minMasks Ds
    · exact ⟨D, hmin, Nat.and_self D⟩
    · have hany : Ds.any (fun D' => !Nat.beq D' D && Nat.beq (Nat.land D' D) D') = true := by
        by_contra hne
        exact hmin (List.mem_filter.2 ⟨hD, by simpa using hne⟩)
      obtain ⟨D', hD', hd⟩ := List.any_eq_true.1 hany
      rw [Bool.and_eq_true] at hd
      have hne : D' ≠ D := fun h => by
        have := hd.1
        rw [h] at this
        simp at this
      have hand : Nat.land D' D = D' := Nat.eq_of_beq_eq_true hd.2
      have hlt : D' < D := lt_of_le_of_ne (by
        have : D' &&& D ≤ D := Nat.and_le_right
        rwa [show D' &&& D = D' from hand] at this) hne
      obtain ⟨M, hM, hMD⟩ := ih D' hlt hD'
      refine ⟨M, hM, ?_⟩
      change M &&& D = M
      have h₁ : M &&& D' = M := hMD
      have h₂ : D' &&& D = D' := hand
      rw [← h₁, Nat.and_assoc, h₂]

/-- What `clos` gives, when it has rows left. -/
theorem clos_spec : ∀ (f : ℕ) (N X rest : List ℕ), (∀ r ∈ rest, derivable X r = false) → (∀ r ∈ rest, r ∉ N ∧ r ∉ X) → (clos f N X rest).2 ≠ [] →
    (∀ x ∈ N, x ∈ (clos f N X rest).1) ∧ (∀ x ∈ X, x ∈ (clos f N X rest).1) ∧ (∀ r ∈ rest, r ∈ (clos f N X rest).1 ∨ r ∈ (clos f N X rest).2) ∧
      (∀ r ∈ (clos f N X rest).2, r ∈ rest) ∧ (∀ r ∈ (clos f N X rest).2, r ∉ (clos f N X rest).1) ∧
      ∀ r ∈ (clos f N X rest).2, derivable (clos f N X rest).1 r = false := by
  intro f
  induction f with
  | zero =>
    intro N X rest _ _ h
    exact absurd rfl h
  | succ f ih =>
    intro N X rest hinv hdisj hne
    have hkeep : ∀ r ∈ rest, derivN N X r = false → derivable (N ++ X) r = false := fun r hr hd => by
      by_contra hc
      rcases derivable_append_of_true (by simpa using hc) with h | h
      · rw [hinv r hr] at h
        exact absurd h (by simp)
      · rw [hd] at h
        exact absurd h (by simp)
    rcases hfilter : rest.filter (derivN N X) with _ | ⟨a, new⟩
    · have hc : clos (f + 1) N X rest = (N ++ X, rest) := by rw [clos, hfilter]
      rw [hc]
      rw [List.filter_eq_nil_iff] at hfilter
      have hf : ∀ r ∈ rest, derivN N X r = false := fun r hr => by simpa using hfilter r hr
      refine ⟨fun x hx => List.mem_append_left _ hx, fun x hx => List.mem_append_right _ hx, fun r hr => Or.inr hr, fun r hr => hr, fun r hr h => ?_, fun r hr => hkeep r hr (hf r hr)⟩
      rcases List.mem_append.1 h with h | h
      · exact (hdisj r hr).1 h
      · exact (hdisj r hr).2 h
    · have hc : clos (f + 1) N X rest = clos f (a :: new) (N ++ X) (rest.filter fun r => !derivN N X r) := by rw [clos, hfilter]
      rw [hc] at hne ⊢
      have hmemnew : ∀ r, r ∈ a :: new ↔ r ∈ rest ∧ derivN N X r = true := fun r => by
        rw [← hfilter, List.mem_filter]
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih (a :: new) (N ++ X) (rest.filter fun r => !derivN N X r)
        (fun r hr => by
          obtain ⟨hr₁, hr₂⟩ := List.mem_filter.1 hr
          exact hkeep r hr₁ (by simpa using hr₂))
        (fun r hr => by
          obtain ⟨hr₁, hr₂⟩ := List.mem_filter.1 hr
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have := ((hmemnew r).1 h).2
            simp [this] at hr₂
          · rcases List.mem_append.1 h with h | h
            · exact (hdisj r hr₁).1 h
            · exact (hdisj r hr₁).2 h) hne
      refine ⟨fun x hx => h₂ x (List.mem_append_left _ hx), fun x hx => h₂ x (List.mem_append_right _ hx), fun r hr => ?_, fun r hr => (List.mem_filter.1 (h₄ r hr)).1, h₅, h₆⟩
      by_cases hd : derivN N X r = true
      · exact Or.inl (h₁ r ((hmemnew r).2 ⟨hr, hd⟩))
      · exact h₃ r (List.mem_filter.2 ⟨hr, by simpa using hd⟩)

theorem mem_dedupN : ∀ (l acc : List ℕ) (x : ℕ), x ∈ l ∨ x ∈ acc → x ∈ dedupN acc l := by
  intro l
  induction l with
  | nil =>
    intro acc x h
    simpa [dedupN] using h
  | cons a l ih =>
    intro acc x h
    rw [dedupN]
    by_cases hm : memN a acc = true
    · rw [hm, Bool.cond_true]
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (memN_iff.1 hm)
        · exact Or.inl h
      · exact Or.inr h
    · rw [Bool.not_eq_true] at hm
      rw [hm, Bool.cond_false]
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_of_mem_pairsOf {p p' : ℕ} : ∀ {X : List ℕ}, (p, p') ∈ pairsOf X → p ∈ X ∧ p' ∈ X := by
  intro X
  induction X with
  | nil => simp [pairsOf]
  | cons a l ih =>
    intro h
    rw [pairsOf] at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨q, hq, he⟩ := List.mem_map.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hq⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

theorem mem_of_mem_coverPairs {P : List (ℕ × ℕ)} {b : ℕ × ℕ} (h : b ∈ coverPairs P) : b ∈ P := by
  rcases List.mem_append.1 h with h | h
  · exact (List.mem_filter.1 h).1
  · exact (List.mem_filter.1 h).1

/-- A number's top bit. -/
theorem testBit_log2 {d : ℕ} (hd : d ≠ 0) : d.testBit (Nat.log2 d) = true := by
  have hlo := Nat.log2_self_le hd
  have hhi := Nat.lt_log2_self (n := d)
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  have hdiv : d / 2 ^ Nat.log2 d = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hlo
    · rw [Nat.pow_succ] at hhi
      omega
  rw [hdiv]

/-- A number with `oneBit` is a power of two. -/
theorem exists_two_pow_of_oneBit {d : ℕ} (h : oneBit d = true) : ∃ j, d = 2 ^ j := by
  rw [oneBit, Bool.and_eq_true] at h
  have h₀ : Nat.land d (d - 1) = 0 := Nat.eq_of_beq_eq_true h.1
  have hd : d ≠ 0 := by
    intro h'
    rw [h'] at h
    simpa using h.2
  refine ⟨Nat.log2 d, ?_⟩
  by_contra hne
  have hlo := Nat.log2_self_le hd
  have hhi := Nat.lt_log2_self (n := d)
  have hb : (d - 1).testBit (Nat.log2 d) = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
    have hlo' : 2 ^ Nat.log2 d ≤ d - 1 := by omega
    have hdiv : (d - 1) / 2 ^ Nat.log2 d = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hlo'
      · rw [Nat.pow_succ] at hhi
        omega
    rw [hdiv]
  have hz : (d &&& (d - 1)).testBit (Nat.log2 d) = false := by
    rw [show d &&& (d - 1) = 0 from h₀, Nat.zero_testBit]
  rw [Nat.testBit_and, testBit_log2 hd, hb] at hz
  simp at hz

theorem oneBit_two_pow (j : ℕ) : oneBit (2 ^ j) = true := by
  have h₀ : Nat.land (2 ^ j) (2 ^ j - 1) = 0 := by
    change (2 ^ j) &&& (2 ^ j - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  unfold oneBit
  rw [h₀, beq_eq_false_of_ne (Nat.two_pow_pos j).ne']
  rfl

/-- A nonzero number with at most the bit `j` is `2 ^ j`. -/
theorem eq_two_pow_of_testBit {e j : ℕ} (hne : e ≠ 0) (h : ∀ k, k ≠ j → e.testBit k = false) : e = 2 ^ j := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  have hij : i = j := by
    by_contra hc
    rw [h i hc] at hi
    simp at hi
  subst hij
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_two_pow]
  by_cases hk : k = i
  · subst hk
    simpa using hi
  · rw [h k hk]
    simp [Ne.symm hk]

theorem testBit_xor' (a b k : ℕ) : (Nat.xor a b).testBit k = (a.testBit k ^^ b.testBit k) := Nat.testBit_xor a b k

theorem testBit_land' (a b k : ℕ) : (Nat.land a b).testBit k = (a.testBit k && b.testBit k) := Nat.testBit_and a b k

theorem land_eq_zero_iff {a b : ℕ} : Nat.land a b = 0 ↔ ∀ k, (a.testBit k && b.testBit k) = false := by
  constructor
  · intro h k
    rw [← testBit_land', h, Nat.zero_testBit]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [testBit_land', h k, Nat.zero_testBit]

/-- **Which sequences give a row in one step.** If `z` is one step from `X`, and with `X` it gives in one step a row that `X` doesn't give, then `progAll` lists it. The pairs `W` cover the mixes of `X`. -/
theorem mem_progAll {m : ℕ} {X : List ℕ} {T : List (ℕ × List ℕ)} {W : List (ℕ × ℕ)} {z r : ℕ} {Ms : List ℕ} (hr : (r, Ms) ∈ T) (hrX : r ∉ X) (hzr : z ≠ r) (hclosed : derivable X r = false)
    (hcov : ∀ p ∈ X, ∃ M ∈ Ms, Nat.land M (Nat.xor r p) = M) (hform : ∀ M ∈ Ms, ∃ p ∈ X, M = Nat.xor r p)
    (hW : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ∃ c ∈ W, c.1 ∈ X ∧ c.2 ∈ X ∧ ∀ k, (u.testBit k = c.1.testBit k ∨ u.testBit k = c.2.testBit k) ∧ (v.testBit k = c.1.testBit k ∨ v.testBit k = c.2.testBit k))
    (hstep : (∃ x ∈ X, ∃ i, z = Nat.xor x (2 ^ i)) ∨ ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ z < 2 ^ m ∧ isMix z u v = true)
    (hd : derivable (z :: X) r = true) : z ∈ progAll m T W X := by
  have hdX : ¬ derivable X r = true := by simp [hclosed]
  have hmixne : ∀ u ∈ X, ∀ v ∈ X, isMix r u v ≠ true := fun u hu v hv h =>
    hdX (derivable_eq_true_iff.2 ⟨u, hu, Or.inr ⟨v, hv, h⟩⟩)
  have hcases : oneStep r z = true ∨ ∃ p ∈ X, isMix r z p = true := by
    obtain ⟨p, hp, hq⟩ := derivable_eq_true_iff.1 hd
    rcases List.mem_cons.1 hp with hpz | hpX
    · subst hpz
      rcases hq with hq | ⟨p', hp', hq⟩
      · exact Or.inl hq
      · rcases List.mem_cons.1 hp' with hp'z | hp'X
        · subst hp'z
          exfalso
          refine hzr (Nat.eq_of_testBit_eq fun k => ?_)
          rcases isMix_iff.1 hq k with h | h <;> exact h.symm
        · exact Or.inr ⟨p', hp'X, hq⟩
    · rcases hq with hq | ⟨p', hp', hq⟩
      · exact absurd (derivable_eq_true_iff.2 ⟨p, hpX, Or.inl hq⟩) hdX
      · rcases List.mem_cons.1 hp' with hp'z | hp'X
        · subst hp'z
          exact Or.inr ⟨p, hpX, by rw [isMix_comm]; exact hq⟩
        · exact absurd hq (hmixne p hpX p' hp'X)
  -- A mask of the row, in the second case.
  have hmask : ∀ p ∈ X, isMix r z p = true → ∃ M ∈ Ms, (∃ p' ∈ X, M = Nat.xor r p') ∧ ∀ k, M.testBit k = true → r.testBit k = z.testBit k := by
    intro p hp hm
    obtain ⟨M, hM, hMD⟩ := hcov p hp
    refine ⟨M, hM, hform M hM, fun k hk => ?_⟩
    have hbit : (Nat.xor r p).testBit k = true := by
      have := congrArg (fun x => Nat.testBit x k) hMD
      simp only [testBit_land', hk, Bool.true_and] at this
      exact this
    rw [testBit_xor'] at hbit
    rcases isMix_iff.1 hm k with h | h
    · exact h
    · rw [h] at hbit
      simp at hbit
  refine mem_dedupN _ _ _ (Or.inl ?_)
  rcases hstep with ⟨x, hx, i, rfl⟩ | ⟨u, hu, v, hv, huv, hzm, hmix⟩
  · -- `z` is one site from `x`.
    refine List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨_, hr, ?_⟩⟩)
    have hxr : Nat.xor r x ≠ 0 := fun h => hrX (by
      have : r = x := Nat.eq_of_testBit_eq fun k => by
        have := congrArg (fun y => Nat.testBit y k) h
        simp only [testBit_xor', Nat.zero_testBit] at this
        cases hr' : r.testBit k <;> cases hx' : x.testBit k <;> simp_all
      rwa [this])
    rcases hcases with hone | ⟨p, hp, hm⟩
    · refine List.mem_append_left _ ?_
      obtain ⟨j, hj⟩ := exists_two_pow_of_oneBit hone
      have hdbit : ∀ k, (Nat.xor r x).testBit k = ((2 ^ j).testBit k ^^ (2 ^ i).testBit k) := fun k => by
        have h₁ := congrArg (fun y => Nat.testBit y k) hj
        simp only [testBit_xor'] at h₁
        rw [testBit_xor']
        generalize r.testBit k = a at h₁ ⊢
        generalize x.testBit k = b at h₁ ⊢
        generalize (2 ^ i).testBit k = c at h₁ ⊢
        generalize (2 ^ j).testBit k = e at h₁ ⊢
        revert h₁
        revert a b c e
        decide
      have hlog := testBit_log2 hxr
      rw [hdbit, Nat.testBit_two_pow, Nat.testBit_two_pow] at hlog
      have hcase : Nat.log2 (Nat.xor r x) = i ∨ Nat.log2 (Nat.xor r x) = j := by
        by_cases h₁ : i = Nat.log2 (Nat.xor r x)
        · exact Or.inl h₁.symm
        · by_cases h₂ : j = Nat.log2 (Nat.xor r x)
          · exact Or.inr h₂.symm
          · rw [decide_eq_false h₁, decide_eq_false h₂] at hlog
            exact absurd hlog (by decide)
      have hremi : Nat.xor (Nat.xor r x) (2 ^ i) = 2 ^ j := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [testBit_xor', hdbit]
        generalize (2 ^ i).testBit k = c
        generalize (2 ^ j).testBit k = e
        revert c e
        decide
      have hremj : Nat.xor (Nat.xor r x) (2 ^ j) = 2 ^ i := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [testBit_xor', hdbit]
        generalize (2 ^ i).testBit k = c
        generalize (2 ^ j).testBit k = e
        revert c e
        decide
      dsimp only
      rcases hcase with h₁ | h₁
      · simp only [h₁, hremi, oneBit_two_pow, Bool.cond_true]
        exact List.mem_cons_self ..
      · simp only [h₁, hremj, oneBit_two_pow, Bool.cond_true]
        exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · obtain ⟨M, hM, ⟨p', hp', hMp⟩, hag⟩ := hmask p hp hm
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨M, hM, ?_⟩)
      have hene : Nat.land (Nat.xor r x) M ≠ 0 := fun h => by
        rw [hMp] at h
        refine hmixne x hx p' hp' ?_
        unfold isMix
        rw [h]
        rfl
      have he : Nat.land (Nat.xor r x) M = 2 ^ i := eq_two_pow_of_testBit hene fun k hk => by
        rw [testBit_land']
        by_cases hMk : M.testBit k = true
        · have := hag k hMk
          rw [testBit_xor'] at this
          rw [testBit_xor', this]
          simp [Ne.symm hk]
        · simp [hMk]
      simp only [he, oneBit_two_pow, Bool.cond_true]
      exact List.mem_cons_self ..
  · -- `z` is a mix of `u`, `v`.
    obtain ⟨c, hc, hc₁, hc₂, hcb⟩ := hW u hu v hv huv
    have hcX : c.1 ∈ X ∧ c.2 ∈ X := ⟨hc₁, hc₂⟩
    have hzc : ∀ k, z.testBit k = c.1.testBit k ∨ z.testBit k = c.2.testBit k := fun k => by
      rcases isMix_iff.1 hmix k with h | h
      · rw [h]
        exact (hcb k).1
      · rw [h]
        exact (hcb k).2
    refine List.mem_append_right _ (List.mem_flatMap.2 ⟨c, hc, List.mem_flatMap.2 ⟨_, hr, ?_⟩⟩)
    have hDne : Nat.land (Nat.xor r c.1) (Nat.xor r c.2) ≠ 0 := fun h => by
      refine hmixne c.1 hcX.1 c.2 hcX.2 ?_
      unfold isMix
      rw [h]
      rfl
    rcases hcases with hone | ⟨p, hp, hm⟩
    · refine List.mem_append_left _ ?_
      obtain ⟨j, hj⟩ := exists_two_pow_of_oneBit hone
      have hrz : ∀ k, k ≠ j → r.testBit k = z.testBit k := fun k hk => by
        have h₁ := congrArg (fun y => Nat.testBit y k) hj
        simp only [testBit_xor', Nat.testBit_two_pow, Ne.symm hk, decide_false] at h₁
        cases hr' : r.testBit k <;> cases hz' : z.testBit k <;> simp_all
      have hD : Nat.land (Nat.xor r c.1) (Nat.xor r c.2) = 2 ^ j := eq_two_pow_of_testBit hDne fun k hk => by
        rw [testBit_land', testBit_xor', testBit_xor', hrz k hk]
        rcases hzc k with h | h <;> rw [h] <;> simp
      simp only [hD, oneBit_two_pow, Bool.cond_true]
      rw [← hj]
      refine List.mem_singleton.2 (Nat.eq_of_testBit_eq fun k => ?_)
      simp only [testBit_xor']
      cases hr' : r.testBit k <;> cases hz' : z.testBit k <;> rfl
    · obtain ⟨M, hM, -, hag⟩ := hmask p hp hm
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨M, hM, ?_⟩)
      have hfeas : Nat.land (Nat.land (Nat.xor r c.1) (Nat.xor r c.2)) M = 0 := land_eq_zero_iff.2 fun k => by
        rw [testBit_land', testBit_xor', testBit_xor']
        by_cases hMk : M.testBit k = true
        · rw [hag k hMk]
          rcases hzc k with h | h <;> rw [h] <;> simp
        · simp [hMk]
      rw [hfeas]
      change z ∈ sub _ _ m
      refine mem_sub m z hzm fun k _ => ?_
      simp only [testBit_xor', testBit_land']
      by_cases hMk : M.testBit k = true
      · left
        rw [hMk, ← hag k hMk]
        cases hr' : r.testBit k <;> cases hc' : c.1.testBit k <;> rfl
      · simp only [Bool.not_eq_true] at hMk
        simpa [hMk] using hzc k

/-! ### From a history to the search -/

section Sound

variable {m : ℕ}

theorem code_inj {r r' : Fin m → Bool} (h : code r = code r') : r = r' := by
  rw [← dec_code r, ← dec_code r', h]

theorem code_eq_xor_of_isFlip {i : Fin m} {p q : Fin m → Bool} (h : IsFlip i p q) : code q = Nat.xor (code p) (2 ^ i.val) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (code q).testBit j = ((code p) ^^^ 2 ^ i.val).testBit j
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : j < m
  · have h₁ := testBit_code q ⟨j, hj⟩
    have h₂ := testBit_code p ⟨j, hj⟩
    simp only at h₁ h₂
    rw [h₁, h₂]
    by_cases hij : i.val = j
    · have : (⟨j, hj⟩ : Fin m) = i := Fin.ext hij.symm
      rw [this, h.1]
      cases p i <;> simp [hij]
    · have : (⟨j, hj⟩ : Fin m) ≠ i := fun h' => hij (by rw [← h'])
      rw [h.2 _ this]
      simp [hij]
  · have hij : i.val ≠ j := by
      have := i.2
      omega
    rw [testBit_code_of_le _ (not_lt.1 hj), testBit_code_of_le _ (not_lt.1 hj)]
    simp [hij]

theorem mem_cands_of_isFlip {X : List ℕ} {i : Fin m} {p q : Fin m → Bool} (h : IsFlip i p q) (hp : code p ∈ X) : code q ∈ cands m X := by
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨code p, hp, List.mem_map.2 ⟨i.val, List.mem_range.2 i.2, ?_⟩⟩)
  exact (code_eq_xor_of_isFlip h).symm

theorem mem_cands_of_mix {X : List ℕ} {p p' q : Fin m → Bool} (h : Recombinant .multiple p p' q) (hp : code p ∈ X) (hp' : code p' ∈ X) (hne : code p ≠ code p') :
    code q ∈ cands m X := by
  have hmix := isMix_iff.1 (isMix_of_isMix h)
  have hkey : ∀ a b, (a = code p ∧ b = code p') ∨ (a = code p' ∧ b = code p) → (a, b) ∈ pairsOf X → code q ∈ cands m X := by
    intro a b hab habm
    obtain ⟨c, hc, hac⟩ := exists_coverPairs habm
    refine List.mem_append_right _ (List.mem_flatMap.2 ⟨c, hc, mem_sub _ _ (code_lt q) fun i _ => ?_⟩)
    have hq : (code q).testBit i = a.testBit i ∨ (code q).testBit i = b.testBit i := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hmix i
      · exact (hmix i).symm
    rcases hac with hac | hac
    · rw [← hac]
      exact hq
    · rw [dominated, Bool.and_eq_true] at hac
      have h₁ := isMix_iff.1 hac.1 i
      have h₂ := isMix_iff.1 hac.2 i
      rcases hq with hq | hq
      · rw [hq]
        exact h₁
      · rw [hq]
        exact h₂
  rcases mem_pairsOf_of_ne hp hp' hne with h' | h'
  · exact hkey _ _ (Or.inl ⟨rfl, rfl⟩) h'
  · exact hkey _ _ (Or.inr ⟨rfl, rfl⟩) h'

variable {S : Fin m → Bool} {A : Finset (Fin m → Bool)} {U : Set (Fin m)} {r : ℕ}

/-- If a history has a label out of `X`, one of them is one step from `X`. -/
theorem exists_step_of_gen (h : Gen .multiple S A U r) {X : List ℕ} (hS : code S ∈ X) (hA : ∃ a ∈ A, code a ∉ X) :
    ∃ q ∈ A, code q ∉ X ∧ ((∃ (i : Fin m) (p : Fin m → Bool), code p ∈ X ∧ IsFlip i p q) ∨ ∃ p p' : Fin m → Bool, code p ∈ X ∧ code p' ∈ X ∧ Recombinant .multiple p p' q) := by
  by_contra hno
  push Not at hno
  obtain ⟨a, ha, hax⟩ := hA
  refine hax (h.mem_of_closed (Y := A) (X := {a | code a ∈ X}) subset_rfl hS (fun i p q hp hq hf => ?_) (fun p p' q hp hp' hq hm => ?_) a ha)
  · by_contra hqX
    exact (hno q hq hqX).1 i p hp hf
  · by_contra hqX
    exact (hno q hq hqX).2 p p' hp hp' hm

/-- A step from `X` shows a sequence one step from `X`, in numbers. -/
theorem derivable_of_step {X : List ℕ} {q : Fin m → Bool}
    (h : (∃ (i : Fin m) (p : Fin m → Bool), code p ∈ X ∧ IsFlip i p q) ∨ ∃ p p' : Fin m → Bool, code p ∈ X ∧ code p' ∈ X ∧ Recombinant .multiple p p' q) :
    derivable X (code q) = true := by
  rcases h with ⟨i, p, hp, hf⟩ | ⟨p, p', hp, hp', hm⟩
  · exact derivable_eq_true_iff.2 ⟨code p, hp, Or.inl (oneStep_of_isFlip hf)⟩
  · exact derivable_eq_true_iff.2 ⟨code p, hp, Or.inr ⟨code p', hp', isMix_of_isMix hm⟩⟩

/-- A step from `X` to a sequence out of `X` is one of the candidates. -/
theorem mem_cands_of_step {X : List ℕ} {q : Fin m → Bool} (hq : code q ∉ X)
    (h : (∃ (i : Fin m) (p : Fin m → Bool), code p ∈ X ∧ IsFlip i p q) ∨ ∃ p p' : Fin m → Bool, code p ∈ X ∧ code p' ∈ X ∧ Recombinant .multiple p p' q) :
    code q ∈ cands m X := by
  rcases h with ⟨i, p, hp, hf⟩ | ⟨p, p', hp, hp', hm⟩
  · exact mem_cands_of_isFlip hf hp
  · refine mem_cands_of_mix hm hp hp' fun he => hq ?_
    obtain rfl := code_inj he
    have : q = p := funext fun i => by
      rcases hm i with h' | h' <;> exact h'
    rw [this]
    exact hp

/-- The pairs `coverPairs (pairsOf X)` cover the mixes of `X`. -/
theorem cover_of_coverPairs {X : List ℕ} :
    ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ∃ c ∈ coverPairs (pairsOf X), c.1 ∈ X ∧ c.2 ∈ X ∧ ∀ k, (u.testBit k = c.1.testBit k ∨ u.testBit k = c.2.testBit k) ∧ (v.testBit k = c.1.testBit k ∨ v.testBit k = c.2.testBit k) := by
  intro u hu v hv huv
  have hkey : ∀ a b, (a = u ∧ b = v) ∨ (a = v ∧ b = u) → (a, b) ∈ pairsOf X → ∃ c ∈ coverPairs (pairsOf X), c.1 ∈ X ∧ c.2 ∈ X ∧ ∀ k, (u.testBit k = c.1.testBit k ∨ u.testBit k = c.2.testBit k) ∧ (v.testBit k = c.1.testBit k ∨ v.testBit k = c.2.testBit k) := by
    intro a b hab habm
    obtain ⟨c, hc, hac⟩ := exists_coverPairs habm
    have hcX := mem_of_mem_pairsOf (p := c.1) (p' := c.2) (mem_of_mem_coverPairs hc)
    refine ⟨c, hc, hcX.1, hcX.2, fun k => ?_⟩
    have hbits : (a.testBit k = c.1.testBit k ∨ a.testBit k = c.2.testBit k) ∧ (b.testBit k = c.1.testBit k ∨ b.testBit k = c.2.testBit k) := by
      rcases hac with hac | hac
      · rw [← hac]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
      · rw [dominated, Bool.and_eq_true] at hac
        exact ⟨isMix_iff.1 hac.1 k, isMix_iff.1 hac.2 k⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbits
    · exact ⟨hbits.2, hbits.1⟩
  rcases mem_pairsOf_of_ne hu hv huv with h | h
  · exact hkey _ _ (Or.inl ⟨rfl, rfl⟩) h
  · exact hkey _ _ (Or.inr ⟨rfl, rfl⟩) h

/-- **The lower bound by the search on two extra labels.** If `S` is a row, `M` has `m + b - 1` rows, with the codes `Mc`, the root generates just `X0` among them, and `level1` says that two extra labels never give all the rows, then `b < R_S(M)`. -/
theorem lt_RS_of_check2 {M : Finset (Fin m → Bool)} {Mc X0 rest0 : List ℕ} {b fuel : ℕ} (hSM : S ∈ M) (hcard : M.card + 1 = m + b)
    (hMc : ∀ x, x ∈ Mc ↔ ∃ r ∈ M, code r = x) (hS : code S ∈ X0) (hpart : ∀ x ∈ Mc, x ∈ X0 ∨ x ∈ rest0)
    (hrest : ∀ r ∈ rest0, r ∈ Mc ∧ r ∉ X0) (hclosed : ∀ r ∈ rest0, derivable X0 r = false) (hne : rest0 ≠ [])
    (hcheck : ∀ z ∈ dedupN [] (cands m X0), level1 fuel m X0 rest0 Mc z = true) : b < RS .multiple S M := by
  by_contra hle
  obtain ⟨a', b', N, hc, hd, hS', hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .multiple S ⟨S, hSM⟩)
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  have hcount' : N.recombCount = RS .multiple S M := hcount
  rw [hS', hcount'] at hg
  have hMA : M ⊆ A := fun r hr => by
    obtain ⟨v, rfl⟩ := hd.displays r hr
    exact hlab v
  have hU : U.ncard ≤ m := by
    have := Set.ncard_le_ncard (Set.subset_univ U)
    simpa [Set.ncard_univ] using this
  have hAcard := hg.card_le
  have hcodeM : ∀ q : Fin m → Bool, code q ∈ Mc ↔ q ∈ M := fun q => by
    rw [hMc]
    constructor
    · rintro ⟨r, hr, he⟩
      rwa [← code_inj he]
    · exact fun h => ⟨q, h, rfl⟩
  have hrow : ∀ x ∈ rest0, ∃ a ∈ M, code a = x := fun x hx => (hMc x).1 (hrest x hx).1
  -- The first extra label.
  obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨a₀, ha₀, ha₀x⟩ := hrow x₀ hx₀
  obtain ⟨q₁, hq₁A, hq₁X, hq₁s⟩ := exists_step_of_gen hg hS ⟨a₀, hMA ha₀, by rw [ha₀x]; exact (hrest x₀ hx₀).2⟩
  have hq₁M : q₁ ∉ M := fun h => by
    rcases hpart _ ((hcodeM q₁).2 h) with h' | h'
    · exact hq₁X h'
    · have := derivable_of_step hq₁s
      rw [hclosed _ h'] at this
      exact absurd this (by simp)
  have hl1 := hcheck _ (mem_dedupN _ _ _ (Or.inl (mem_cands_of_step hq₁X hq₁s)))
  rw [level1, memN_eq_false_iff.2 (fun h => hq₁M ((hcodeM q₁).1 h)), memN_eq_false_iff.2 hq₁X] at hl1
  simp only [Bool.false_or] at hl1
  rw [level1', Bool.and_eq_true] at hl1
  obtain ⟨hl1₁, hl1₂⟩ := hl1
  have hne1 : (clos fuel [code q₁] X0 rest0).2 ≠ [] := by simpa using hl1₁
  have hdisj1 : ∀ r ∈ rest0, r ∉ [code q₁] ∧ r ∉ X0 := fun r hr => ⟨fun h => by
    rw [List.mem_singleton.1 h] at hr
    exact hq₁M ((hcodeM q₁).1 (hrest _ hr).1), (hrest r hr).2⟩
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := clos_spec fuel [code q₁] X0 rest0 hclosed hdisj1 hne1
  generalize hcl : clos fuel [code q₁] X0 rest0 = c at c₁ c₂ c₃ c₄ c₅ c₆ hne1 hl1₂
  obtain ⟨X1, rest1⟩ := c
  simp only at c₁ c₂ c₃ c₄ c₅ c₆ hne1 hl1₂
  -- The second extra label.
  have hS1 : code S ∈ X1 := c₂ _ hS
  obtain ⟨x₁, hx₁⟩ := List.exists_mem_of_ne_nil _ hne1
  obtain ⟨a₁, ha₁, ha₁x⟩ := hrow x₁ (c₄ x₁ hx₁)
  obtain ⟨q₂, hq₂A, hq₂X, hq₂s⟩ := exists_step_of_gen hg hS1 ⟨a₁, hMA ha₁, by rw [ha₁x]; exact c₅ x₁ hx₁⟩
  have hq₂M : q₂ ∉ M := fun h => by
    rcases hpart _ ((hcodeM q₂).2 h) with h' | h'
    · exact hq₂X (c₂ _ h')
    · rcases c₃ _ h' with h₈ | h₈
      · exact hq₂X h₈
      · have := derivable_of_step hq₂s
        rw [c₆ _ h₈] at this
        exact absurd this (by simp)
  have hq₁q₂ : q₁ ≠ q₂ := fun h => hq₂X (by
    rw [← h]
    exact c₁ _ (List.mem_singleton.2 rfl))
  -- There are no other labels.
  have hAeq : A = insert q₁ (insert q₂ M) := by
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.insert_subset hq₁A (Finset.insert_subset hq₂A hMA)) ?_
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hq₂M]
    · omega
    · simp [hq₁q₂, hq₁M]
  -- The third step fails.
  have hfinal : ∀ (X2 rest2 : List ℕ), (∀ x ∈ X1, x ∈ X2) → code q₂ ∈ X2 → (∀ r ∈ rest1, r ∈ X2 ∨ r ∈ rest2) → (∀ r ∈ rest2, r ∈ rest1) → (∀ r ∈ rest2, r ∉ X2) →
      (∀ r ∈ rest2, derivable X2 r = false) → rest2 ≠ [] → False := by
    intro X2 rest2 h₁ h₂ h₃ h₄ h₅ h₆ h₇
    obtain ⟨x₂, hx₂⟩ := List.exists_mem_of_ne_nil _ h₇
    obtain ⟨a₂, ha₂, ha₂x⟩ := hrow x₂ (c₄ x₂ (h₄ x₂ hx₂))
    obtain ⟨q₃, hq₃A, hq₃X, hq₃s⟩ := exists_step_of_gen hg (h₁ _ hS1) ⟨a₂, hMA ha₂, by rw [ha₂x]; exact h₅ x₂ hx₂⟩
    rw [hAeq] at hq₃A
    rcases Finset.mem_insert.1 hq₃A with rfl | hq₃A
    · exact hq₃X (h₁ _ (c₁ _ (List.mem_singleton.2 rfl)))
    rcases Finset.mem_insert.1 hq₃A with rfl | hq₃A
    · exact hq₃X h₂
    rcases hpart _ ((hcodeM q₃).2 hq₃A) with h' | h'
    · exact hq₃X (h₁ _ (c₂ _ h'))
    rcases c₃ _ h' with h₈ | h₈
    · exact hq₃X (h₁ _ h₈)
    rcases h₃ _ h₈ with h₉ | h₉
    · exact hq₃X h₉
    · have := derivable_of_step hq₃s
      rw [h₆ _ h₉] at this
      exact absurd this (by simp)
  have hq₂rest : ∀ r ∈ rest1, code q₂ ≠ r := fun r hr h => by
    rw [← h] at hr
    exact hq₂M ((hcodeM q₂).1 (hrest _ (c₄ _ hr)).1)
  by_cases hprog : code q₂ ∈ progAll m (table rest1 X1) (coverPairs (pairsOf X1)) X1
  · have hl2 := List.all_eq_true.1 hl1₂ _ hprog
    rw [level2, Bool.or_eq_true, Bool.or_eq_true, memN_iff, memN_iff] at hl2
    rcases hl2 with (hl2 | hl2) | hl2
    · exact hq₂M ((hcodeM q₂).1 hl2)
    · exact hq₂X hl2
    · have hne2 : (clos fuel [code q₂] X1 rest1).2 ≠ [] := by simpa using hl2
      obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := clos_spec fuel [code q₂] X1 rest1 c₆ (fun r hr => ⟨fun h => hq₂rest r hr (List.mem_singleton.1 h).symm, c₅ r hr⟩) hne2
      exact hfinal _ _ d₂ (d₁ _ (List.mem_singleton.2 rfl)) d₃ d₄ d₅ d₆ hne2
  · refine hfinal (code q₂ :: X1) rest1 (fun x hx => List.mem_cons_of_mem _ hx) (List.mem_cons_self ..) (fun r hr => Or.inr hr) (fun r hr => hr) (fun r hr h => ?_)
      (fun r hr => ?_) hne1
    · rcases List.mem_cons.1 h with h | h
      · exact hq₂rest r hr h.symm
      · exact c₅ r hr h
    · by_contra hd'
      have hcov : ∀ p ∈ X1, ∃ M ∈ minMasks (X1.map fun p => Nat.xor r p), Nat.land M (Nat.xor r p) = M := fun p hp =>
        exists_minMasks _ (List.mem_map.2 ⟨p, hp, rfl⟩)
      have hform : ∀ M ∈ minMasks (X1.map fun p => Nat.xor r p), ∃ p ∈ X1, M = Nat.xor r p := fun M hM => by
        obtain ⟨p, hp, he⟩ := List.mem_map.1 (List.mem_filter.1 hM).1
        exact ⟨p, hp, he.symm⟩
      refine hprog (mem_progAll (r := r) (Ms := minMasks (X1.map fun p => Nat.xor r p)) (List.mem_map.2 ⟨r, hr, rfl⟩) (c₅ r hr) (hq₂rest r hr) (c₆ r hr) hcov hform cover_of_coverPairs ?_ (by simpa using hd'))
      rcases hq₂s with ⟨i, p, hp, hf⟩ | ⟨p, p', hp, hp', hm⟩
      · exact Or.inl ⟨code p, hp, i.val, code_eq_xor_of_isFlip hf⟩
      · refine Or.inr ⟨code p, hp, code p', hp', fun he => hq₂X ?_, code_lt q₂, isMix_of_isMix hm⟩
        obtain rfl := code_inj he
        have : q₂ = p := funext fun i => by
          rcases hm i with h' | h' <;> exact h'
        rw [this]
        exact hp

/-- **The lower bound with no extra label.** If `S` is a row, `M` has `1 + m + b` rows, with the codes `Mc`, and the root generates just `X0` among them, then `b < R_S(M)`. -/
theorem lt_RS_of_closed {M : Finset (Fin m → Bool)} {Mc X0 rest0 : List ℕ} {b : ℕ} (hSM : S ∈ M) (hcard : M.card = 1 + m + b)
    (hMc : ∀ x, x ∈ Mc ↔ ∃ r ∈ M, code r = x) (hS : code S ∈ X0) (hpart : ∀ x ∈ Mc, x ∈ X0 ∨ x ∈ rest0)
    (hrest : ∀ r ∈ rest0, r ∈ Mc ∧ r ∉ X0) (hclosed : ∀ r ∈ rest0, derivable X0 r = false) (hne : rest0 ≠ []) : b < RS .multiple S M := by
  by_contra hle
  obtain ⟨a', b', N, hc, hd, hS', hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .multiple S ⟨S, hSM⟩)
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  have hcount' : N.recombCount = RS .multiple S M := hcount
  rw [hS', hcount'] at hg
  have hMA : M ⊆ A := fun r hr => by
    obtain ⟨v, rfl⟩ := hd.displays r hr
    exact hlab v
  have hU : U.ncard ≤ m := by
    have := Set.ncard_le_ncard (Set.subset_univ U)
    simpa [Set.ncard_univ] using this
  have hAcard := hg.card_le
  have hAeq : M = A := Finset.eq_of_subset_of_card_le hMA (by omega)
  have hcodeM : ∀ q : Fin m → Bool, code q ∈ Mc ↔ q ∈ M := fun q => by
    rw [hMc]
    constructor
    · rintro ⟨r, hr, he⟩
      rwa [← code_inj he]
    · exact fun h => ⟨q, h, rfl⟩
  obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨a₀, ha₀, ha₀x⟩ := (hMc x₀).1 (hrest x₀ hx₀).1
  obtain ⟨q, hqA, hqX, hqs⟩ := exists_step_of_gen hg hS ⟨a₀, hMA ha₀, by rw [ha₀x]; exact (hrest x₀ hx₀).2⟩
  rcases hpart _ ((hcodeM q).2 (hAeq ▸ hqA)) with h' | h'
  · exact hqX h'
  · have := derivable_of_step hqs
    rw [hclosed _ h'] at this
    exact absurd this (by simp)

end Sound

/-! ### Histories from lists -/

/-- A step of a history, in numbers: change the site `i` of `p`, or take `q`, a mix of `p`, `p'`. -/
inductive Step where
  | flip (p i : ℕ)
  | mix (p p' q : ℕ)

/-- The labels that a list of steps adds. -/
def Step.label : Step → ℕ
  | .flip p i => Nat.xor p (2 ^ i)
  | .mix _ _ q => q

/-- The number of recombinations of a list of steps. -/
def mixCount : List Step → ℕ
  | [] => 0
  | .flip _ _ :: l => mixCount l
  | .mix _ _ _ :: l => mixCount l + 1

/-- The steps can be carried out, from the labels `done`, with the sites `used` already used. -/
def runOK (m : ℕ) : List ℕ → List ℕ → List Step → Bool
  | _, _, [] => true
  | done, used, .flip p i :: l =>
    memN p done && !memN i used && Nat.blt i m && runOK m (Nat.xor p (2 ^ i) :: done) (i :: used) l
  | done, used, .mix p p' q :: l =>
    memN p done && memN p' done && isMix q p p' && Nat.blt q (2 ^ m) && runOK m (q :: done) used l

section Run

/-- A flip adds its label to a history. -/
theorem Gen.exists_flip {κ : Type*} [LinearOrder κ] {c : Crossover} {S : κ → Bool} {A : Finset (κ → Bool)} {U : Set κ} {r : ℕ} (h : Gen c S A U r) {p q : κ → Bool} {i : κ}
    (hp : p ∈ A) (hi : i ∉ U) (hf : IsFlip i p q) : ∃ A' : Finset (κ → Bool), Gen c S A' (insert i U) r ∧ A ⊆ A' ∧ q ∈ A' :=
  ⟨insert q A, h.flip hp hi hf, Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩

/-- A recombination adds its label to a history. -/
theorem Gen.exists_recomb {κ : Type*} [LinearOrder κ] {c : Crossover} {S : κ → Bool} {A : Finset (κ → Bool)} {U : Set κ} {r : ℕ} (h : Gen c S A U r) {p p' q : κ → Bool}
    (hp : p ∈ A) (hp' : p' ∈ A) (hm : Recombinant c p p' q) : ∃ A' : Finset (κ → Bool), Gen c S A' U (r + 1) ∧ A ⊆ A' ∧ q ∈ A' :=
  ⟨insert q A, h.recomb hp hp' hm, Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩

variable {m : ℕ}

theorem isFlip_dec {p i : ℕ} (hi : i < m) : IsFlip (⟨i, hi⟩ : Fin m) (dec p) (dec (Nat.xor p (2 ^ i))) := by
  refine ⟨?_, fun j hj => ?_⟩
  · change (p ^^^ 2 ^ i).testBit i = !p.testBit i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    simp
  · change (p ^^^ 2 ^ i).testBit j.val = p.testBit j.val
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    have : i ≠ j.val := fun h => hj (Fin.ext h.symm)
    simp [this]

theorem recombinant_dec {p p' q : ℕ} (h : isMix q p p' = true) : Recombinant .multiple (dec p : Fin m → Bool) (dec p') (dec q) :=
  fun i => isMix_iff.1 h i.val

theorem xor_lt_two_pow {p i : ℕ} (hp : p < 2 ^ m) (hi : i < m) : Nat.xor p (2 ^ i) < 2 ^ m :=
  Nat.xor_lt_two_pow hp (Nat.pow_lt_pow_right (by decide) hi)

/-- A list of steps that can be carried out is a history. -/
theorem exists_gen_of_run {S : Fin m → Bool} : ∀ (l : List Step) (done used : List ℕ) (A : Finset (Fin m → Bool)) (U : Set (Fin m)) (r : ℕ), Gen .multiple S A U r →
    (∀ x ∈ done, x < 2 ^ m ∧ (dec x : Fin m → Bool) ∈ A) → (∀ i : Fin m, i ∈ U → i.val ∈ used) → runOK m done used l = true →
    ∃ (A' : Finset (Fin m → Bool)) (U' : Set (Fin m)), Gen .multiple S A' U' (r + mixCount l) ∧ A ⊆ A' ∧ ∀ s ∈ l, (dec s.label : Fin m → Bool) ∈ A' := by
  intro l
  induction l with
  | nil =>
    intro done used A U r hg _ _ _
    exact ⟨A, U, hg, subset_rfl, by simp⟩
  | cons s l ih =>
    intro done used A U r hg hdone hused hrun
    cases s with
    | flip p i =>
      simp only [runOK, Bool.and_eq_true, Bool.not_eq_true'] at hrun
      obtain ⟨⟨⟨hp, hi⟩, him⟩, hrun⟩ := hrun
      have him' : i < m := by simpa [Nat.blt] using him
      have hp' := hdone p (memN_iff.1 hp)
      have hiU : (⟨i, him'⟩ : Fin m) ∉ U := fun h => by
        have := hused _ h
        rw [memN_eq_false_iff] at hi
        exact hi this
      obtain ⟨A₁, hg', hsub, hmem⟩ := Gen.exists_flip hg hp'.2 hiU (isFlip_dec him')
      obtain ⟨A', U', h₁, h₂, h₃⟩ := ih (Nat.xor p (2 ^ i) :: done) (i :: used) _ _ r hg' (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨xor_lt_two_pow hp'.1 him', hmem⟩
        · exact ⟨(hdone x hx).1, hsub (hdone x hx).2⟩) (fun j hj => by
        rcases hj with rfl | hj
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hused j hj)) hrun
      refine ⟨A', U', h₁, hsub.trans h₂, fun s' hs' => ?_⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact h₂ hmem
      · exact h₃ s' hs'
    | mix p p' q =>
      simp only [runOK, Bool.and_eq_true] at hrun
      obtain ⟨⟨⟨⟨hp, hp'⟩, hq⟩, hqm⟩, hrun⟩ := hrun
      have hqm' : q < 2 ^ m := by simpa [Nat.blt] using hqm
      obtain ⟨A₁, hg', hsub, hmem⟩ := Gen.exists_recomb hg (hdone p (memN_iff.1 hp)).2 (hdone p' (memN_iff.1 hp')).2 (recombinant_dec hq)
      obtain ⟨A', U', h₁, h₂, h₃⟩ := ih (q :: done) used _ _ (r + 1) hg' (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hqm', hmem⟩
        · exact ⟨(hdone x hx).1, hsub (hdone x hx).2⟩) hused hrun
      refine ⟨A', U', ?_, hsub.trans h₂, fun s' hs' => ?_⟩
      · have : r + mixCount (Step.mix p p' q :: l) = r + 1 + mixCount l := by
          simp only [mixCount]
          omega
        rw [this]
        exact h₁
      · rcases List.mem_cons.1 hs' with rfl | hs'
        · exact h₂ hmem
        · exact h₃ s' hs'

/-- **The upper bound from a list of steps.** -/
theorem RS_le_of_run {s : ℕ} (hs : s < 2 ^ m) {l : List Step} (hrun : runOK m [s] [] l = true) {M : Finset (Fin m → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hrows : ∀ r ∈ M, r = dec s ∨ ∃ t ∈ l, r = dec t.label) : RS .multiple (dec s) M ≤ mixCount l := by
  obtain ⟨A', U', h₁, h₂, h₃⟩ := exists_gen_of_run (S := (dec s : Fin m → Bool)) l [s] [] {dec s} ∅ 0 Gen.base (fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact ⟨hs, Finset.mem_singleton_self _⟩) (fun _ h => absurd h (Set.notMem_empty _)) hrun
  rw [Nat.zero_add] at h₁
  refine h₁.RS_le_of_subset (fun r hr => ?_) hM hC
  rcases hrows r hr with rfl | ⟨t, ht, rfl⟩
  · exact h₂ (Finset.mem_singleton_self _)
  · exact h₃ t ht

end Run

end LabelSearch

end Gusfield2007
