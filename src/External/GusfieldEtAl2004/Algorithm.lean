module

public import External.GusfieldEtAl2004.GallFromChains
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The decision algorithm of Gusfield, Eddhu, Langley 2004 (Sections 3.1, 3.2, 7)

See the `README.md` of this directory. `galledDecide S M` is a computable function. It builds the conflict graph, finds its components, and runs the Site-Arrangement Algorithm of Section 3.2 on each non-trivial one. Each function here returns its value and the number of entries of the matrix it read, or labels it wrote, so the count is of what the
function does (`galledDecide_ops_le`).

`galledDecide_iff` is the correctness, both ways: it says `true` exactly when `M` has a galled tree with ancestral sequence `S` and single crossovers. By `exists_reduced_of_decide`, a reduced galled tree then exists. `galledBuild` in `Build.lean` returns one.
-/

@[expose] public section

namespace GusfieldEtAl2004.Algorithm

/-- A row. -/
abbrev Row (m : ℕ) := Fin m → Bool

variable {m : ℕ} {β : Type*}

/-- `all`, with the cost of the tests added up. There is no early exit, so the count doesn't depend on the answers. -/
def allOps (l : List β) (p : β → Bool × ℕ) : Bool × ℕ := (l.all fun b => (p b).1, (l.map fun b => (p b).2).sum)

/-- `any`, with the cost of the tests added up. -/
def anyOps (l : List β) (p : β → Bool × ℕ) : Bool × ℕ := (l.any fun b => (p b).1, (l.map fun b => (p b).2).sum)

/-- `filter`, with the cost of the tests added up. -/
def filterOps (l : List β) (p : β → Bool × ℕ) : List β × ℕ := (l.filter fun b => (p b).1, (l.map fun b => (p b).2).sum)

/-- A `1` of the source: another state than the ancestral sequence's. -/
def flipAt (S r : Row m) (i : Fin m) : Bool := r i != S i

/-- Two rows agree on the sites `C`. -/
def eqOn (C : List (Fin m)) (a b : Row m) : Bool × ℕ := allOps C fun i => (a i == b i, 1)

/-- The `1`s of `a` on `C` are `1`s of `b`. -/
def subOn (S : Row m) (C : List (Fin m)) (a b : Row m) : Bool × ℕ := allOps C fun i => (!flipAt S a i || flipAt S b i, 1)

/-- The rows have no `1` in common on `C`. -/
def disjOn (S : Row m) (C : List (Fin m)) (a b : Row m) : Bool × ℕ := allOps C fun i => (!(flipAt S a i && flipAt S b i), 1)

/-- The `1`s of one row on `C` are among those of the other. -/
def cmpOn (S : Row m) (C : List (Fin m)) (a b : Row m) : Bool × ℕ := ((subOn S C a b).1 || (subOn S C b a).1, (subOn S C a b).2 + (subOn S C b a).2)

/-- The rows, one for each restriction to `C`. -/
def distinctOn (C : List (Fin m)) : List (Row m) → List (Row m) × ℕ
  | [] => ([], 0)
  | a :: t =>
    let t' := distinctOn C t
    let c := anyOps t'.1 (eqOn C a)
    (if c.1 then t'.1 else a :: t'.1, t'.2 + c.2)

/-- The state of the end of a chain at a site: a `1` if some row of the chain has one. -/
def topAt (S : Row m) (X : List (Row m)) (i : Fin m) : Bool := if X.any (fun r => flipAt S r i) then !S i else S i

/-- `s` is the recombination at the point `n` of the ends of `B` (the prefix) and `A` (the suffix), on `C`. -/
def recombOk (S : Row m) (C : List (Fin m)) (A B : List (Row m)) (s : Row m) (n : ℕ) : Bool × ℕ :=
  allOps C fun i => (s i == if i.val < n then topAt S B i else topAt S A i, A.length + B.length + 1)

/-- Step 3 of the **Site-Arrangement Algorithm**: with the rows equal to `s` on `C` removed, the others are a perfect phylogeny in one or two paths, with all the sites of `C`, and `s` is a recombination of the two ends. The recombination point isn't taken from the bipartition of Lemma 3.1, as in the source, but tried: that test can only accept the points that the source's does. -/
def candidate (S : Row m) (C : List (Fin m)) (rows : List (Row m)) (s : Row m) : Bool × ℕ :=
  let rest := filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)
  match rest.1 with
  | [] => (false, rest.2)
  | seed :: _ =>
    let A := filterOps rest.1 (cmpOn S C seed)
    let B := filterOps rest.1 fun r => (!(cmpOn S C seed r).1, (cmpOn S C seed r).2)
    let chA := allOps A.1 fun a => allOps A.1 (cmpOn S C a)
    let chB := allOps B.1 fun a => allOps B.1 (cmpOn S C a)
    let dj := allOps A.1 fun a => allOps B.1 (disjOn S C a)
    let cov := allOps C fun i => (A.1.any (fun r => flipAt S r i) || B.1.any (fun r => flipAt S r i), A.1.length + B.1.length)
    let rc := anyOps (List.range (m + 1)) fun n => ((recombOk S C A.1 B.1 s n).1 || (recombOk S C B.1 A.1 s n).1, (recombOk S C A.1 B.1 s n).2 + (recombOk S C B.1 A.1 s n).2)
    (chA.1 && chB.1 && dj.1 && cov.1 && rc.1, rest.2 + A.2 + B.2 + chA.2 + chB.2 + dj.2 + cov.2 + rc.2)

/-- The **Site-Arrangement Algorithm** on a component `C`: some row passes. -/
def compTest (S : Row m) (M : List (Row m)) (C : List (Fin m)) : Bool × ℕ :=
  let nz := filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)
  let rows := distinctOn C nz.1
  let t := anyOps rows.1 (candidate S C rows.1)
  (t.1, nz.2 + rows.2 + t.2)

/-- A row has a pair of states at two sites: two entries read in each row. -/
def hasPair (M : List (Row m)) (i j : Fin m) (a b : Bool) : Bool × ℕ := anyOps M fun r => (r i == a && r j == b, 2)

/-- **Definition 2.1** of the source: the columns `i`, `j` conflict: the rows have the three pairs other than the ancestral one. -/
def conflictOps (S : Row m) (M : List (Row m)) (i j : Fin m) : Bool × ℕ :=
  ((hasPair M i j (!S i) (!S j)).1 && (hasPair M i j (!S i) (S j)).1 && (hasPair M i j (S i) (!S j)).1,
    (hasPair M i j (!S i) (!S j)).2 + (hasPair M i j (!S i) (S j)).2 + (hasPair M i j (S i) (!S j)).2)

/-- The edges of the conflict graph (Definition 2.3 of the source). -/
def edgesOps (S : Row m) (M : List (Row m)) : List (Fin m × Fin m) × ℕ :=
  filterOps ((List.finRange m).product (List.finRange m)) fun e => conflictOps S M e.1 e.2

/-- The label of a site in a table of labels. -/
def labAt (t : List (Fin m)) (k : Fin m) : Fin m := t.getD k.val k

/-- The table of the labels of the components, merging the ends of the edges one at a time: each edge rewrites the `m` labels. -/
def labTable : List (Fin m × Fin m) → List (Fin m)
  | [] => List.finRange m
  | e :: es =>
    let t := labTable es
    let a := labAt t e.2
    let b := labAt t e.1
    t.map fun c => if c = a then b else c

/-- The labels of the components. -/
def labOf (es : List (Fin m × Fin m)) : Fin m → Fin m :=
  let t := labTable es
  fun k => labAt t k

/-- The test on one label: nothing to do for an isolated site, and the Site-Arrangement Algorithm on a non-trivial component. -/
def labelTest (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (c : Fin m) : Bool × ℕ :=
  let C := (List.finRange m).filter fun k => f k = c
  if C.length ≤ 1 then (true, m) else ((compTest S M C).1, m + (compTest S M C).2)

/-- **The decision.** The conflict graph, its components, and the arrangement of each non-trivial component. `.1` is the answer, and `.2` the number of operations. -/
def galledDecide (S : Row m) (M : List (Row m)) : Bool × ℕ :=
  let es := edgesOps S M
  let f := labOf es.1
  let reps := (((List.finRange m).map f)).dedup
  let t := allOps reps (labelTest S M f)
  (t.1, es.2 + m * es.1.length + m * m + t.2)

/-! ### The count -/

theorem sum_map_le {l : List β} {g : β → ℕ} {c : ℕ} (h : ∀ b ∈ l, g b ≤ c) : (l.map g).sum ≤ l.length * c := by
  have := List.sum_le_length_nsmul (l.map g) c (by simpa using h)
  simpa using this

theorem allOps_le {l : List β} {p : β → Bool × ℕ} {c : ℕ} (h : ∀ b ∈ l, (p b).2 ≤ c) : (allOps l p).2 ≤ l.length * c := sum_map_le h

theorem anyOps_le {l : List β} {p : β → Bool × ℕ} {c : ℕ} (h : ∀ b ∈ l, (p b).2 ≤ c) : (anyOps l p).2 ≤ l.length * c := sum_map_le h

theorem filterOps_le {l : List β} {p : β → Bool × ℕ} {c : ℕ} (h : ∀ b ∈ l, (p b).2 ≤ c) : (filterOps l p).2 ≤ l.length * c := sum_map_le h

theorem filterOps_length_le {l : List β} {p : β → Bool × ℕ} : (filterOps l p).1.length ≤ l.length := List.length_filter_le _ _

theorem eqOn_le (C : List (Fin m)) (a b : Row m) : (eqOn C a b).2 ≤ C.length := by
  have h := allOps_le (l := C) (p := fun i => (a i == b i, 1)) (c := 1) fun _ _ => le_rfl
  rw [mul_one] at h
  exact h

theorem subOn_le (S : Row m) (C : List (Fin m)) (a b : Row m) : (subOn S C a b).2 ≤ C.length := by
  have h := allOps_le (l := C) (p := fun i => (!flipAt S a i || flipAt S b i, 1)) (c := 1) fun _ _ => le_rfl
  rw [mul_one] at h
  exact h

theorem disjOn_le (S : Row m) (C : List (Fin m)) (a b : Row m) : (disjOn S C a b).2 ≤ C.length := by
  have h := allOps_le (l := C) (p := fun i => (!(flipAt S a i && flipAt S b i), 1)) (c := 1) fun _ _ => le_rfl
  rw [mul_one] at h
  exact h

theorem cmpOn_le (S : Row m) (C : List (Fin m)) (a b : Row m) : (cmpOn S C a b).2 ≤ 2 * C.length := by
  have h₁ := subOn_le S C a b
  have h₂ := subOn_le S C b a
  simp only [cmpOn]
  omega

theorem distinctOn_length_le (C : List (Fin m)) (l : List (Row m)) : (distinctOn C l).1.length ≤ l.length := by
  induction l with
  | nil => simp [distinctOn]
  | cons a t ih =>
    simp only [distinctOn]
    split_ifs <;> simp <;> omega

theorem distinctOn_le (C : List (Fin m)) (l : List (Row m)) : (distinctOn C l).2 ≤ l.length * (l.length * C.length) := by
  induction l with
  | nil => simp [distinctOn]
  | cons a t ih =>
    simp only [distinctOn, List.length_cons]
    have h₁ : (anyOps (distinctOn C t).1 (eqOn C a)).2 ≤ (distinctOn C t).1.length * C.length := anyOps_le fun b _ => eqOn_le C a b
    have h₂ := distinctOn_length_le C t
    have h₃ : (distinctOn C t).1.length * C.length ≤ t.length * C.length := Nat.mul_le_mul_right _ h₂
    nlinarith [Nat.zero_le (t.length * C.length), Nat.zero_le (t.length * (t.length * C.length)), Nat.zero_le C.length]

theorem recombOk_le (S : Row m) (C : List (Fin m)) (A B : List (Row m)) (s : Row m) (n : ℕ) : (recombOk S C A B s n).2 ≤ C.length * (A.length + B.length + 1) :=
  allOps_le fun _ _ => le_rfl

/-- The cost of one candidate, for `n` rows and `|C| ≤ m`. -/
theorem candidate_le (S : Row m) {C : List (Fin m)} (hC : C.length ≤ m) (rows : List (Row m)) (s : Row m) {n : ℕ} (hn : rows.length ≤ n) :
    (candidate S C rows s).2 ≤ 7 * (n * n * m) + 4 * (n * m) + 3 * (n * m) + (m + 1) * (2 * (m * (2 * n + 1))) + n * m + m * (2 * n) := by
  have hmulC : ∀ {x y : ℕ}, x ≤ y → x * C.length ≤ y * m := fun h => Nat.mul_le_mul h hC
  have hrest : (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).2 ≤ n * m := (filterOps_le (c := C.length) fun b _ => eqOn_le C b s).trans (hmulC hn)
  have hrestL : (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1.length ≤ n := filterOps_length_le.trans hn
  unfold candidate
  generalize hR : filterOps rows (fun r => (!(eqOn C r s).1, (eqOn C r s).2)) = R at hrest hrestL
  dsimp only
  cases hlist : R.1 with
  | nil =>
    dsimp only
    nlinarith [Nat.zero_le (n * n * m), Nat.zero_le (n * m), Nat.zero_le (m * (2 * n))]
  | cons seed tl =>
    dsimp only
    rw [hlist] at hrestL
    obtain ⟨l, hl⟩ : ∃ l, l = seed :: tl := ⟨_, rfl⟩
    rw [← hl] at hrestL ⊢
    have hA : (filterOps l (cmpOn S C seed)).2 ≤ n * (2 * m) := (filterOps_le (c := 2 * C.length) fun b _ => cmpOn_le S C seed b).trans (Nat.mul_le_mul hrestL (by omega))
    have hB : (filterOps l fun r => (!(cmpOn S C seed r).1, (cmpOn S C seed r).2)).2 ≤ n * (2 * m) := (filterOps_le (c := 2 * C.length) fun b _ => cmpOn_le S C seed b).trans (Nat.mul_le_mul hrestL (by omega))
    have hAL : (filterOps l (cmpOn S C seed)).1.length ≤ n := filterOps_length_le.trans hrestL
    have hBL : (filterOps l fun r => (!(cmpOn S C seed r).1, (cmpOn S C seed r).2)).1.length ≤ n := filterOps_length_le.trans hrestL
    generalize (filterOps l (cmpOn S C seed)) = A at hA hAL
    generalize (filterOps l fun r => (!(cmpOn S C seed r).1, (cmpOn S C seed r).2)) = B at hB hBL
    have hch : ∀ X : List (Row m), X.length ≤ n → (allOps X fun a => allOps X (cmpOn S C a)).2 ≤ n * (n * (2 * m)) := by
      intro X hX
      refine (allOps_le (c := n * (2 * m)) fun a _ => (allOps_le (c := 2 * m) fun b _ => (cmpOn_le S C a b).trans (by omega)).trans (Nat.mul_le_mul_right _ hX)).trans (Nat.mul_le_mul_right _ hX)
    have hdj : (allOps A.1 fun a => allOps B.1 (disjOn S C a)).2 ≤ n * (n * m) :=
      (allOps_le (c := n * m) fun a _ => (allOps_le (c := m) fun b _ => (disjOn_le S C a b).trans hC).trans (Nat.mul_le_mul_right _ hBL)).trans (Nat.mul_le_mul_right _ hAL)
    have hcov : (allOps C fun i => (A.1.any (fun r => flipAt S r i) || B.1.any (fun r => flipAt S r i), A.1.length + B.1.length)).2 ≤ m * (2 * n) :=
      (allOps_le (c := 2 * n) fun _ _ => by dsimp only; omega).trans (Nat.mul_le_mul_right _ hC)
    have hrc : (anyOps (List.range (m + 1)) fun n' => ((recombOk S C A.1 B.1 s n').1 || (recombOk S C B.1 A.1 s n').1, (recombOk S C A.1 B.1 s n').2 + (recombOk S C B.1 A.1 s n').2)).2 ≤ (m + 1) * (2 * (m * (2 * n + 1))) := by
      have hone : ∀ n', (recombOk S C A.1 B.1 s n').2 + (recombOk S C B.1 A.1 s n').2 ≤ 2 * (m * (2 * n + 1)) := by
        intro n'
        have h₁ := recombOk_le S C A.1 B.1 s n'
        have h₂ := recombOk_le S C B.1 A.1 s n'
        have h₃ : C.length * (A.1.length + B.1.length + 1) ≤ m * (2 * n + 1) := Nat.mul_le_mul hC (by omega)
        have h₄ : C.length * (B.1.length + A.1.length + 1) ≤ m * (2 * n + 1) := Nat.mul_le_mul hC (by omega)
        omega
      simpa using anyOps_le (l := List.range (m + 1)) (c := 2 * (m * (2 * n + 1))) fun n' _ => hone n'
    have hchA := hch A.1 hAL
    have hchB := hch B.1 hBL
    have heq : n * (n * (2 * m)) = 2 * (n * n * m) := by ring
    have heq' : n * (n * m) = n * n * m := by ring
    have heq'' : n * (2 * m) = 2 * (n * m) := by ring
    omega

/-! ### What the tests mean -/

theorem eqOn_iff {C : List (Fin m)} {a b : Row m} : (eqOn C a b).1 = true ↔ ∀ i ∈ C, a i = b i := by
  simp [eqOn, allOps]

theorem subOn_iff {S : Row m} {C : List (Fin m)} {a b : Row m} : (subOn S C a b).1 = true ↔ ∀ i ∈ C, a i ≠ S i → b i ≠ S i := by
  simp only [subOn, allOps, List.all_eq_true, flipAt]
  refine forall₂_congr fun i _ => ?_
  cases a i <;> cases b i <;> cases S i <;> simp

theorem disjOn_iff {S : Row m} {C : List (Fin m)} {a b : Row m} : (disjOn S C a b).1 = true ↔ ∀ i ∈ C, a i ≠ S i → b i = S i := by
  simp only [disjOn, allOps, List.all_eq_true, flipAt]
  refine forall₂_congr fun i _ => ?_
  cases a i <;> cases b i <;> cases S i <;> simp

theorem cmpOn_iff {S : Row m} {C : List (Fin m)} {a b : Row m} : (cmpOn S C a b).1 = true ↔ (∀ i ∈ C, a i ≠ S i → b i ≠ S i) ∨ ∀ i ∈ C, b i ≠ S i → a i ≠ S i := by
  simp only [cmpOn, Bool.or_eq_true, subOn_iff]

theorem mem_of_mem_distinctOn {C : List (Fin m)} {l : List (Row m)} {r : Row m} (h : r ∈ (distinctOn C l).1) : r ∈ l := by
  induction l with
  | nil => simp [distinctOn] at h
  | cons a t ih =>
    simp only [distinctOn] at h
    split_ifs at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h')

theorem exists_mem_distinctOn {C : List (Fin m)} {l : List (Row m)} {r : Row m} (h : r ∈ l) : ∃ r' ∈ (distinctOn C l).1, ∀ i ∈ C, r' i = r i := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [distinctOn]
    rcases List.mem_cons.1 h with rfl | h'
    · split_ifs with hc
      · simp only [anyOps, List.any_eq_true] at hc
        obtain ⟨b, hb, hab⟩ := hc
        exact ⟨b, hb, fun i hi => (eqOn_iff.1 hab i hi).symm⟩
      · exact ⟨r, List.mem_cons_self, fun _ _ => rfl⟩
    · obtain ⟨r', hr', hrr⟩ := ih h'
      split_ifs
      · exact ⟨r', hr', hrr⟩
      · exact ⟨r', List.mem_cons_of_mem _ hr', hrr⟩

theorem topAt_ne_iff {S : Row m} {X : List (Row m)} {i : Fin m} : topAt S X i ≠ S i ↔ ∃ r ∈ X, r i ≠ S i := by
  have hany : X.any (fun r => flipAt S r i) = true ↔ ∃ r ∈ X, r i ≠ S i := by
    simp [flipAt]
  by_cases h : X.any (fun r => flipAt S r i) = true
  · simp only [topAt, h, ite_true, hany.1 h, iff_true]
    cases S i <;> simp
  · have hno : ¬ ∃ r ∈ X, r i ≠ S i := fun h' => h (hany.2 h')
    simp [topAt, h, hno]

theorem hasPair_iff {M : List (Row m)} {i j : Fin m} {a b : Bool} : (hasPair M i j a b).1 = true ↔ ∃ r ∈ M, r i = a ∧ r j = b := by
  simp [hasPair, anyOps]

open Gusfield2007 in
/-- The test for a conflict is `Conflict`. -/
theorem conflictOps_iff {S : Row m} {M : List (Row m)} {i j : Fin m} : (conflictOps S M i j).1 = true ↔ Conflict S M.toFinset i j := by
  simp only [conflictOps, Bool.and_eq_true, hasPair_iff]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩ a b hab
    have hcases : ∀ u v : Bool, u = v ∨ u = !v := by decide
    rcases hcases a (S i) with rfl | rfl <;> rcases hcases b (S j) with rfl | rfl
    · simp at hab
    · obtain ⟨r, hr, h₄⟩ := h₃
      exact ⟨r, List.mem_toFinset.2 hr, h₄⟩
    · obtain ⟨r, hr, h₄⟩ := h₂
      exact ⟨r, List.mem_toFinset.2 hr, h₄⟩
    · obtain ⟨r, hr, h₄⟩ := h₁
      exact ⟨r, List.mem_toFinset.2 hr, h₄⟩
  · intro h
    have hne : ∀ b : Bool, (!b) ≠ b := by decide
    have hc : ∀ a b, (a ≠ S i ∨ b ≠ S j) → ∃ r ∈ M, r i = a ∧ r j = b := fun a b hab => by
      obtain ⟨r, hr, h₄⟩ := h a b hab
      exact ⟨r, List.mem_toFinset.1 hr, h₄⟩
    exact ⟨⟨hc _ _ (Or.inl (hne _)), hc _ _ (Or.inl (hne _))⟩, hc _ _ (Or.inr (hne _))⟩

/-- The function that the table holds, which the proofs below are about. -/
def labFun : List (Fin m × Fin m) → Fin m → Fin m
  | [] => id
  | e :: es => fun k => if labFun es k = labFun es e.2 then labFun es e.1 else labFun es k

theorem labAt_ofFn (f : Fin m → Fin m) (k : Fin m) : labAt (List.ofFn f) k = f k := by
  simp [labAt, List.getD_eq_getElem?_getD]

theorem labTable_eq (es : List (Fin m × Fin m)) : labTable es = List.ofFn (labFun es) := by
  induction es with
  | nil =>
    simp only [labTable, labFun]
    exact (List.ofFn_id m).symm
  | cons e es ih =>
    simp only [labTable, ih, labAt_ofFn, labFun, List.map_ofFn]
    congr

theorem labOf_eq (es : List (Fin m × Fin m)) : labOf es = labFun es := by
  funext k
  simp only [labOf, labTable_eq, labAt_ofFn]

/-- **The components.** The labels of `labOf` are equal only on sites joined by the edges, and are equal at the two ends of each edge. -/
theorem labOf_spec {G : SimpleGraph (Fin m)} {es : List (Fin m × Fin m)} (hes : ∀ e ∈ es, G.Adj e.1 e.2) :
    (∀ k l, labOf es k = labOf es l → G.Reachable k l) ∧ ∀ e ∈ es, labOf es e.1 = labOf es e.2 := by
  induction es with
  | nil =>
    refine ⟨fun k l h => ?_, by simp⟩
    rw [labOf_eq] at h
    rw [show k = l from h]
  | cons e es ih =>
    obtain ⟨ih₁, ih₂⟩ := ih fun e' he' => hes e' (List.mem_cons_of_mem _ he')
    have hadj := hes e List.mem_cons_self
    have hf : labOf (e :: es) = fun k => if labOf es k = labOf es e.2 then labOf es e.1 else labOf es k := by
      simp only [labOf_eq, labFun]
    rw [hf]
    constructor
    · intro k l hkl
      dsimp only at hkl
      by_cases hk : labOf es k = labOf es e.2 <;> by_cases hl : labOf es l = labOf es e.2
      · exact ih₁ k l (hk.trans hl.symm)
      · rw [ite_eq_left hk, ite_eq_right hl] at hkl
        exact (ih₁ _ _ hk).trans (hadj.symm.reachable.trans (ih₁ _ _ hkl))
      · rw [ite_eq_right hk, ite_eq_left hl] at hkl
        exact (ih₁ _ _ hkl).trans (hadj.reachable.trans (ih₁ _ _ hl.symm))
      · rw [ite_eq_right hk, ite_eq_right hl] at hkl
        exact ih₁ k l hkl
    · intro e' he'
      dsimp only
      rcases List.mem_cons.1 he' with rfl | he''
      · by_cases h₁ : labOf es e'.1 = labOf es e'.2
        · simp [h₁]
        · simp [h₁]
      · have h₁ := ih₂ e' he''
        rw [h₁]

/-- The labels of `labOf` on all the edges of a graph are its connected components. -/
theorem labOf_iff {G : SimpleGraph (Fin m)} {es : List (Fin m × Fin m)} (hes : ∀ e ∈ es, G.Adj e.1 e.2) (hall : ∀ i j, G.Adj i j → (i, j) ∈ es) (k l : Fin m) :
    labOf es k = labOf es l ↔ G.Reachable k l := by
  obtain ⟨h₁, h₂⟩ := labOf_spec hes
  refine ⟨h₁ k l, fun h => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hab ih => exact ih.trans (h₂ _ (hall _ _ hab))

theorem edgesOps_spec {S : Row m} {M : List (Row m)} (i j : Fin m) : (i, j) ∈ (edgesOps S M).1 ↔ (Gusfield2007.conflictGraph S M.toFinset).Adj i j := by
  simp only [edgesOps, filterOps, List.mem_filter, List.pair_mem_product, List.mem_finRange, true_and, conflictOps_iff]
  rfl

/-! ### If the test passes, there is a gall -/

section Sound

open scoped Classical

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

/-- **Sound on a component**: if the Site-Arrangement Algorithm accepts, then a network for the rows of the component, with one recombination node, exists. -/
theorem exists_piece_of_compTest (c : (incompatGraph (addRow M.toFinset S)).ConnectedComponent) {Cl : List (Fin m)} (hCl : ∀ i, i ∈ Cl ↔ i ∈ c.supp) (ht : (compTest S M Cl).1 = true) :
    ∃ (a b : ℕ) (P : Network c.supp (Fin a) (Fin b)), P.Obeys .single ∧ P.ancestral = c.supp.domRestrict S ∧ P.Derives ((restrictRows c.supp (addRow M.toFinset S)).erase (c.supp.domRestrict S)) ∧ P.recombCount ≤ 1 := by
  -- restrictions to the component
  have hconv : ∀ {a b : Row m}, c.supp.domRestrict a = c.supp.domRestrict b ↔ ∀ i ∈ Cl, a i = b i := by
    intro a b
    constructor
    · intro h i hi
      exact congrFun h ⟨i, (hCl i).1 hi⟩
    · intro h
      funext i
      exact h i.1 ((hCl i.1).2 i.2)
  have hconvne : ∀ {a b : Row m} {i : c.supp}, c.supp.domRestrict a i ≠ c.supp.domRestrict b i ↔ a i.1 ≠ b i.1 := Iff.rfl
  have hsub : ∀ {a b : Row m}, fl (c.supp.domRestrict S) (c.supp.domRestrict a) ⊆ fl (c.supp.domRestrict S) (c.supp.domRestrict b) ↔ ∀ i ∈ Cl, a i ≠ S i → b i ≠ S i := by
    intro a b
    constructor
    · intro h i hi hai
      exact h (show c.supp.domRestrict a ⟨i, (hCl i).1 hi⟩ ≠ c.supp.domRestrict S ⟨i, (hCl i).1 hi⟩ from hai)
    · intro h i hai
      exact h i.1 ((hCl i.1).2 i.2) hai
  simp only [compTest, anyOps, List.any_eq_true] at ht
  obtain ⟨s, hsr, hcand⟩ := ht
  set nz := (filterOps M fun r => (!(eqOn Cl r S).1, (eqOn Cl r S).2)).1 with hnz
  set rows := (distinctOn Cl nz).1 with hrows
  have hnzM : ∀ {r}, r ∈ nz → r ∈ M ∧ ¬ ∀ i ∈ Cl, r i = S i := by
    intro r hr
    obtain ⟨h₁, h₂⟩ := List.mem_filter.1 hr
    refine ⟨h₁, fun h₃ => ?_⟩
    have := eqOn_iff.2 h₃
    simp [this] at h₂
  have hrowsM : ∀ {r}, r ∈ rows → r ∈ M ∧ ¬ ∀ i ∈ Cl, r i = S i := fun hr => hnzM (mem_of_mem_distinctOn hr)
  unfold candidate at hcand
  dsimp only at hcand
  set rest := (filterOps rows fun r => (!(eqOn Cl r s).1, (eqOn Cl r s).2)).1 with hrest
  have hrestProp : ∀ {r}, r ∈ rest → r ∈ rows ∧ ¬ ∀ i ∈ Cl, r i = s i := by
    intro r hr
    obtain ⟨h₁, h₂⟩ := List.mem_filter.1 hr
    refine ⟨h₁, fun h₃ => ?_⟩
    have := eqOn_iff.2 h₃
    simp [this] at h₂
  cases hrl : rest with
  | nil =>
    rw [hrl] at hcand
    simp at hcand
  | cons seed tl =>
    rw [hrl] at hcand
    dsimp only at hcand
    rw [← hrl] at hcand
    have hseed : seed ∈ rest := by rw [hrl]; exact List.mem_cons_self
    set A := (filterOps rest (cmpOn S Cl seed)).1 with hA
    set B := (filterOps rest fun r => (!(cmpOn S Cl seed r).1, (cmpOn S Cl seed r).2)).1 with hB
    simp only [Bool.and_eq_true, allOps, anyOps, List.all_eq_true, List.any_eq_true, Bool.or_eq_true] at hcand
    obtain ⟨⟨⟨⟨hchA, hchB⟩, hdj⟩, hcov⟩, n, -, hrc⟩ := hcand
    have hArest : ∀ {r}, r ∈ A → r ∈ rest := fun hr => (List.mem_filter.1 hr).1
    have hBrest : ∀ {r}, r ∈ B → r ∈ rest := fun hr => (List.mem_filter.1 hr).1
    have hsplit : ∀ {r}, r ∈ rest → r ∈ A ∨ r ∈ B := by
      intro r hr
      by_cases h : (cmpOn S Cl seed r).1 = true
      · exact Or.inl (List.mem_filter.2 ⟨hr, h⟩)
      · exact Or.inr (List.mem_filter.2 ⟨hr, by simpa using h⟩)
    let conv : Row m → (c.supp → Bool) := c.supp.domRestrict
    let A' : Finset (c.supp → Bool) := (A.map conv).toFinset
    let B' : Finset (c.supp → Bool) := (B.map conv).toFinset
    have hmemA' : ∀ {u}, u ∈ A' ↔ ∃ r ∈ A, conv r = u := by
      intro u
      simp [A']
    have hmemB' : ∀ {u}, u ∈ B' ↔ ∃ r ∈ B, conv r = u := by
      intro u
      simp [B']
    have hneS : ∀ {r}, r ∈ rest → conv r ≠ conv S := by
      intro r hr h
      exact (hrowsM (hrestProp hr).1).2 (hconv.1 h)
    have hneSs : conv s ≠ conv S := fun h => (hrowsM hsr).2 (hconv.1 h)
    have hnes : ∀ {r}, r ∈ rest → conv r ≠ conv s := fun hr h => (hrestProp hr).2 (hconv.1 h)
    have hchain : ∀ {X : List (Row m)}, (∀ {r}, r ∈ X → r ∈ rest) → (∀ a ∈ X, ∀ b ∈ X, (cmpOn S Cl a b).1 = true) → IsChain (conv S) (X.map conv).toFinset := by
      intro X hX hch
      refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
      · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ X, conv a = u := by simpa using hu
        obtain ⟨b, hb, rfl⟩ : ∃ b ∈ X, conv b = v := by simpa using hv
        rcases cmpOn_iff.1 (hch a ha b hb) with h | h
        · exact Or.inl (hsub.2 h)
        · exact Or.inr (hsub.2 h)
      · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ X, conv a = u := by simpa using hu
        exact hneS (hX ha)
    have hchA' : IsChain (conv S) A' := hchain hArest hchA
    have hchB' : IsChain (conv S) B' := hchain hBrest hchB
    have hdisj : ∀ u ∈ A', ∀ v ∈ B', ∀ i, u i ≠ conv S i → v i = conv S i := by
      intro u hu v hv i hi
      obtain ⟨a, ha, rfl⟩ := hmemA'.1 hu
      obtain ⟨b, hb, rfl⟩ := hmemB'.1 hv
      exact disjOn_iff.1 (hdj a ha b hb) i.1 ((hCl i.1).2 i.2) hi
    have hdisj' : ∀ u ∈ B', ∀ v ∈ A', ∀ i, u i ≠ conv S i → v i = conv S i := by
      intro u hu v hv i hi
      by_contra hne
      exact hi (hdisj v hv u hu i hne)
    have hne' : (A' ∪ B').Nonempty := by
      have hsA : seed ∈ A := List.mem_filter.2 ⟨hseed, cmpOn_iff.2 (Or.inl fun _ _ h => h)⟩
      exact ⟨conv seed, Finset.mem_union_left _ (hmemA'.2 ⟨seed, hsA, rfl⟩)⟩
    have hcov' : ∀ i : c.supp, ∃ r ∈ A' ∪ B', r i ≠ conv S i := by
      intro i
      have h := hcov i.1 ((hCl i.1).2 i.2)
      rcases h with ⟨r, hr, hri⟩ | ⟨r, hr, hri⟩
      · refine ⟨conv r, Finset.mem_union_left _ (hmemA'.2 ⟨r, hr, rfl⟩), ?_⟩
        change r i.1 ≠ S i.1
        simpa [flipAt] using hri
      · refine ⟨conv r, Finset.mem_union_right _ (hmemB'.2 ⟨r, hr, rfl⟩), ?_⟩
        change r i.1 ≠ S i.1
        simpa [flipAt] using hri
    have hsA' : conv s ∉ A' := fun h => by
      obtain ⟨r, hr, hrs⟩ := hmemA'.1 h
      exact hnes (hArest hr) hrs
    have hsB' : conv s ∉ B' := fun h => by
      obtain ⟨r, hr, hrs⟩ := hmemB'.1 h
      exact hnes (hBrest hr) hrs
    -- the ends of the chains
    have htop : ∀ (X : List (Row m)) (i : c.supp), topRow (conv S) (X.map conv).toFinset i = topAt S X i.1 := by
      intro X i
      have hcases : ∀ {u v : Bool}, (u ≠ v ↔ (X.any (fun r => flipAt S r i.1) = true)) → (v = S i.1) → (if X.any (fun r => flipAt S r i.1) = true then !S i.1 else S i.1) = u := by
        intro u v h hv
        subst hv
        by_cases hany : X.any (fun r => flipAt S r i.1) = true
        · have := h.2 hany
          simp only [hany, ite_true]
          revert this
          cases u <;> cases S i.1 <;> simp
        · have hu : u = S i.1 := by
            by_contra hne
            exact hany (h.1 hne)
          simp [hany, hu]
      have hiff : topRow (conv S) (X.map conv).toFinset i ≠ S i.1 ↔ X.any (fun r => flipAt S r i.1) = true := by
        have h₁ := topRow_ne_iff (S₀ := conv S) (X := (X.map conv).toFinset) (i := i)
        have h₂ : (∃ r ∈ (X.map conv).toFinset, r i ≠ conv S i) ↔ X.any (fun r => flipAt S r i.1) = true := by
          simp [flipAt, conv, Set.domRestrict]
        exact h₁.trans h₂
      exact (hcases hiff rfl).symm.trans (rfl)
    have hrecomb : ∀ {X Y : List (Row m)}, (recombOk S Cl X Y s n).1 = true → Recombinant .single (topRow (conv S) (Y.map conv).toFinset) (topRow (conv S) (X.map conv).toFinset) (conv s) := by
      intro X Y h
      simp only [recombOk, allOps, List.all_eq_true, beq_iff_eq] at h
      let L₀ : LowerSet c.supp := ⟨{i | i.1.val < n}, fun u v huv hu => lt_of_le_of_lt (show v.1.val ≤ u.1.val from huv) hu⟩
      refine ⟨L₀, fun i => ?_⟩
      have h₁ := h i.1 ((hCl i.1).2 i.2)
      by_cases hi : i.1.val < n
      · have hi' : i ∈ L₀ := hi
        simp only [hi, ite_true] at h₁
        rw [ite_eq_left hi', htop Y i]
        exact h₁
      · have hi' : i ∉ L₀ := hi
        simp only [hi, ite_false] at h₁
        rw [ite_eq_right hi', htop X i]
        exact h₁
    obtain ⟨a, b, P, h₁, h₂, h₃, h₄⟩ : ∃ (a b : ℕ) (P : Network c.supp (Fin a) (Fin b)), P.Obeys .single ∧ P.ancestral = conv S ∧ P.Derives (insert (conv s) (A' ∪ B')) ∧ P.recombCount ≤ 1 := by
      rcases hrc with h | h
      · exact IsArrangement.exists_network ⟨hchA', hchB', hdisj, hne', hcov', hsA', hsB', hneSs, hrecomb h⟩
      · have harr : IsArrangement (conv S) (conv s) B' A' .single := ⟨hchB', hchA', hdisj', by rwa [Finset.union_comm], by
          intro i
          obtain ⟨r, hr, hri⟩ := hcov' i
          exact ⟨r, by rwa [Finset.union_comm], hri⟩, hsB', hsA', hneSs, hrecomb h⟩
        obtain ⟨a, b, P, h₁, h₂, h₃, h₄⟩ := harr.exists_network
        exact ⟨a, b, P, h₁, h₂, by rwa [Finset.union_comm] at h₃, h₄⟩
    refine ⟨a, b, P, h₁, h₂, ?_, h₄⟩
    have hT : (restrictRows c.supp (addRow M.toFinset S)).erase (c.supp.domRestrict S) = insert (conv s) (A' ∪ B') := by
      ext u
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨hne, hu⟩
        obtain ⟨ρ, hρ, rfl⟩ := mem_restrictRows.1 hu
        rcases mem_addRow.1 hρ with rfl | hρ
        · exact absurd rfl hne
        · have hρM : ρ ∈ M := List.mem_toFinset.1 hρ
          have hρnz : ρ ∈ nz := List.mem_filter.2 ⟨hρM, by
            have : ¬ (eqOn Cl ρ S).1 = true := fun h' => hne (hconv.2 (eqOn_iff.1 h'))
            simpa using this⟩
          obtain ⟨ρ', hρ', hρe⟩ := exists_mem_distinctOn (C := Cl) hρnz
          have hconvρ : c.supp.domRestrict ρ = conv ρ' := (hconv.2 hρe).symm
          by_cases hρs : ∀ i ∈ Cl, ρ' i = s i
          · exact Or.inl (hconvρ.trans (hconv.2 hρs))
          · have hρrest : ρ' ∈ rest := List.mem_filter.2 ⟨hρ', by
              have : ¬ (eqOn Cl ρ' s).1 = true := fun h' => hρs (eqOn_iff.1 h')
              simpa using this⟩
            rcases hsplit hρrest with h' | h'
            · exact Or.inr (Or.inl (hmemA'.2 ⟨ρ', h', hconvρ.symm⟩))
            · exact Or.inr (Or.inr (hmemB'.2 ⟨ρ', h', hconvρ.symm⟩))
      · have hin : ∀ {r}, r ∈ M → c.supp.domRestrict r ∈ restrictRows c.supp (addRow M.toFinset S) := by
          intro r hr
          exact mem_restrictRows.2 ⟨r, mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr)), rfl⟩
        rintro (rfl | hu | hu)
        · exact ⟨hneSs, hin (hrowsM hsr).1⟩
        · obtain ⟨r, hr, rfl⟩ := hmemA'.1 hu
          exact ⟨hneS (hArest hr), hin (hrowsM (hrestProp (hArest hr)).1).1⟩
        · obtain ⟨r, hr, rfl⟩ := hmemB'.1 hu
          exact ⟨hneS (hBrest hr), hin (hrowsM (hrestProp (hBrest hr)).1).1⟩
    rw [hT]
    exact h₃

end Sound

/-! ### If there is a galled tree, the test passes -/

section Complete

open scoped Classical

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {V E : Type*} {N : Network (Fin m) V E} [Finite V] {M : List (Row m)}

/-- A lower set of the sites is a recombination point. -/
theorem exists_point (L₀ : LowerSet (Fin m)) : ∃ n, n ≤ m ∧ ∀ i : Fin m, i ∈ L₀ ↔ i.val < n := by
  by_cases hall : ∀ i : Fin m, i ∈ L₀
  · exact ⟨m, le_rfl, fun i => ⟨fun _ => i.2, fun _ => hall i⟩⟩
  · push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hex : ∃ k, ∃ i : Fin m, i.val = k ∧ i ∉ L₀ := ⟨i₀.val, i₀, rfl, hi₀⟩
    refine ⟨Nat.find hex, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · obtain ⟨i, hi, -⟩ := Nat.find_spec hex
      rw [← hi]
      exact i.2.le
    · by_contra hge
      push Not at hge
      obtain ⟨j, hj, hjL⟩ := Nat.find_spec hex
      exact hjL (L₀.lower (show j ≤ i from by rw [Fin.le_def, hj]; exact hge) hi)
    · by_contra hiL
      exact Nat.find_min hex hi ⟨i, rfl, hiL⟩

/-- **The test on an arrangement.** Rows at two sides, with chains on each side, no site in common across, and `s` a recombination of the ends: `candidate` accepts `s`. -/
theorem candidate_of_sides {S : Row m} {C : List (Fin m)} {rows : List (Row m)} {s : Row m} {SP SQ : Row m → Prop} {tP tQ : Row m} (hne : C ≠ [])
    (h₁ : ∀ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) → SP r ∨ SQ r)
    (hPP : ∀ a b, SP a → SP b → (∀ i ∈ C, a i ≠ S i → b i ≠ S i) ∨ ∀ i ∈ C, b i ≠ S i → a i ≠ S i)
    (hQQ : ∀ a b, SQ a → SQ b → (∀ i ∈ C, a i ≠ S i → b i ≠ S i) ∨ ∀ i ∈ C, b i ≠ S i → a i ≠ S i)
    (hPQ : ∀ a b, SP a → SQ b → ∀ i ∈ C, a i ≠ S i → b i = S i) (hQP : ∀ a b, SQ a → SP b → ∀ i ∈ C, a i ≠ S i → b i = S i)
    (hfl : ∀ r ∈ rows, ∃ i ∈ C, r i ≠ S i) (hcov : ∀ i ∈ C, ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ r i ≠ S i)
    (htP : ∀ i ∈ C, tP i ≠ S i ↔ ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ SP r ∧ r i ≠ S i) (htQ : ∀ i ∈ C, tQ i ≠ S i ↔ ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ SQ r ∧ r i ≠ S i)
    (hrc : ∃ n, n ≤ m ∧ ((∀ i ∈ C, s i = if i.val < n then tQ i else tP i) ∨ ∀ i ∈ C, s i = if i.val < n then tP i else tQ i)) : (candidate S C rows s).1 = true := by
  have hrest : ∀ {r}, r ∈ (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 ↔ r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i := by
    intro r
    simp only [filterOps, List.mem_filter, Bool.not_eq_true', ← eqOn_iff, Bool.not_eq_true]
  have hbool : ∀ {a b c : Bool}, (a ≠ c ↔ b ≠ c) → a = b := by decide
  have core : ∀ {SP SQ : Row m → Prop} {tP tQ : Row m}, (∀ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) → SP r ∨ SQ r) →
      (∀ a b, SP a → SP b → (∀ i ∈ C, a i ≠ S i → b i ≠ S i) ∨ ∀ i ∈ C, b i ≠ S i → a i ≠ S i) →
      (∀ a b, SQ a → SQ b → (∀ i ∈ C, a i ≠ S i → b i ≠ S i) ∨ ∀ i ∈ C, b i ≠ S i → a i ≠ S i) →
      (∀ a b, SP a → SQ b → ∀ i ∈ C, a i ≠ S i → b i = S i) → (∀ a b, SQ a → SP b → ∀ i ∈ C, a i ≠ S i → b i = S i) →
      (∀ i ∈ C, tP i ≠ S i ↔ ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ SP r ∧ r i ≠ S i) → (∀ i ∈ C, tQ i ≠ S i ↔ ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ SQ r ∧ r i ≠ S i) →
      (∃ n, n ≤ m ∧ ((∀ i ∈ C, s i = if i.val < n then tQ i else tP i) ∨ ∀ i ∈ C, s i = if i.val < n then tP i else tQ i)) →
      ∀ seed tl, (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 = seed :: tl → SP seed → (candidate S C rows s).1 = true := by
    intro SP SQ tP tQ h₁ hPP hQQ hPQ hQP htP htQ hrc seed tl hl hseed
    have hseedR : seed ∈ rows ∧ ¬ ∀ i ∈ C, seed i = s i := hrest.1 (by rw [hl]; exact List.mem_cons_self)
    obtain ⟨is, his, hisf⟩ := hfl seed hseedR.1
    have hnotcmp : ∀ r, r ∈ rows → SQ r → (cmpOn S C seed r).1 = false := by
      intro r hr hrQ
      obtain ⟨ir, hir, hirf⟩ := hfl r hr
      rw [← Bool.not_eq_true, cmpOn_iff]
      rintro (h | h)
      · exact h is his hisf (hPQ seed r hseed hrQ is his hisf)
      · exact h ir hir hirf (hQP r seed hrQ hseed ir hir hirf)
    have hmemA : ∀ {r}, r ∈ (filterOps (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 (cmpOn S C seed)).1 ↔ (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ SP r := by
      intro r
      change r ∈ List.filter (fun b => (cmpOn S C seed b).1) _ ↔ _
      rw [List.mem_filter, hrest]
      constructor
      · rintro ⟨hr, hcmp⟩
        refine ⟨hr, ?_⟩
        rcases h₁ r hr with h | h
        · exact h
        · rw [hnotcmp r hr.1 h] at hcmp
          exact absurd hcmp (by simp)
      · rintro ⟨hr, hrP⟩
        exact ⟨hr, cmpOn_iff.2 (hPP seed r hseed hrP)⟩
    have hmemB : ∀ {r}, r ∈ (filterOps (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 fun r => (!(cmpOn S C seed r).1, (cmpOn S C seed r).2)).1 ↔ (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ SQ r := by
      intro r
      change r ∈ List.filter (fun b => !(cmpOn S C seed b).1) _ ↔ _
      rw [List.mem_filter, hrest]
      constructor
      · rintro ⟨hr, hcmp⟩
        refine ⟨hr, ?_⟩
        rcases h₁ r hr with h | h
        · rw [cmpOn_iff.2 (hPP seed r hseed h)] at hcmp
          exact absurd hcmp (by simp)
        · exact h
      · rintro ⟨hr, hrQ⟩
        refine ⟨hr, ?_⟩
        rw [hnotcmp r hr.1 hrQ]
        rfl
    unfold candidate
    dsimp only
    rw [hl]
    dsimp only
    rw [← hl]
    generalize hA : (filterOps (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 (cmpOn S C seed)) = A at hmemA
    generalize hB : (filterOps (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 fun r => (!(cmpOn S C seed r).1, (cmpOn S C seed r).2)) = B at hmemB
    have htopA : ∀ i ∈ C, topAt S A.1 i = tP i := by
      intro i hi
      refine hbool (c := S i) (topAt_ne_iff.trans ?_)
      rw [htP i hi]
      exact ⟨fun ⟨r, hr, hri⟩ => ⟨r, (hmemA.1 hr).1, (hmemA.1 hr).2, hri⟩, fun ⟨r, hr, hrP, hri⟩ => ⟨r, hmemA.2 ⟨hr, hrP⟩, hri⟩⟩
    have htopB : ∀ i ∈ C, topAt S B.1 i = tQ i := by
      intro i hi
      refine hbool (c := S i) (topAt_ne_iff.trans ?_)
      rw [htQ i hi]
      exact ⟨fun ⟨r, hr, hri⟩ => ⟨r, (hmemB.1 hr).1, (hmemB.1 hr).2, hri⟩, fun ⟨r, hr, hrP, hri⟩ => ⟨r, hmemB.2 ⟨hr, hrP⟩, hri⟩⟩
    simp only [Bool.and_eq_true, allOps, anyOps, List.all_eq_true, List.any_eq_true, Bool.or_eq_true]
    refine ⟨⟨⟨⟨fun a ha b hb => cmpOn_iff.2 (hPP a b (hmemA.1 ha).2 (hmemA.1 hb).2), fun a ha b hb => cmpOn_iff.2 (hQQ a b (hmemB.1 ha).2 (hmemB.1 hb).2)⟩,
      fun a ha b hb => disjOn_iff.2 (hPQ a b (hmemA.1 ha).2 (hmemB.1 hb).2)⟩, fun i hi => ?_⟩, ?_⟩
    · obtain ⟨r, hr, hri⟩ := hcov i hi
      have hfr : flipAt S r i = true := by simpa [flipAt] using hri
      rcases h₁ r hr with h | h
      · exact Or.inl ⟨r, hmemA.2 ⟨hr, h⟩, hfr⟩
      · exact Or.inr ⟨r, hmemB.2 ⟨hr, h⟩, hfr⟩
    · obtain ⟨n, hn, hn'⟩ := hrc
      refine ⟨n, List.mem_range.2 (by omega), ?_⟩
      rcases hn' with h | h
      · refine Or.inl ?_
        simp only [recombOk, allOps, List.all_eq_true, beq_iff_eq]
        intro i hi
        rw [htopA i hi, htopB i hi]
        exact h i hi
      · refine Or.inr ?_
        simp only [recombOk, allOps, List.all_eq_true, beq_iff_eq]
        intro i hi
        rw [htopA i hi, htopB i hi]
        exact h i hi
  obtain ⟨ih, hih⟩ := List.exists_mem_of_ne_nil C hne
  obtain ⟨r₀, hr₀, -⟩ := hcov ih hih
  cases hl : (filterOps rows fun r => (!(eqOn C r s).1, (eqOn C r s).2)).1 with
  | nil =>
    have := hrest.2 hr₀
    rw [hl] at this
    simp at this
  | cons seed tl =>
    have hseedR : seed ∈ rows ∧ ¬ ∀ i ∈ C, seed i = s i := hrest.1 (by rw [hl]; exact List.mem_cons_self)
    rcases h₁ seed hseedR with h | h
    · exact core h₁ hPP hQQ hPQ hQP htP htQ hrc seed tl hl h
    · refine core (SP := SQ) (SQ := SP) (tP := tQ) (tQ := tP) (fun r hr => (h₁ r hr).symm) hQQ hPP hQP hPQ htQ htP ?_ seed tl hl h
      obtain ⟨n, hn, hn'⟩ := hrc
      exact ⟨n, hn, hn'.symm⟩

/-- The rows of a component, on one gall: which side of the gall a row is at, on the sites `C`. -/
def AtSide (N : Network (Fin m) V E) (S : Row m) (C : List (Fin m)) (P : List E) (r : Row m) : Prop :=
  ∃ c d, P = c ++ d ∧ ∀ i ∈ C, r i ≠ S i ↔ N.site i ∈ c

omit [Finite V] in
theorem AtSide.comparable {S : Row m} {C : List (Fin m)} {P : List E} {a b : Row m} (ha : AtSide N S C P a) (hb : AtSide N S C P b) :
    (∀ i ∈ C, a i ≠ S i → b i ≠ S i) ∨ ∀ i ∈ C, b i ≠ S i → a i ≠ S i := by
  obtain ⟨c, d, hP, hc⟩ := ha
  obtain ⟨c', d', hP', hc'⟩ := hb
  have h₁ : c <+: P := ⟨d, hP.symm⟩
  have h₂ : c' <+: P := ⟨d', hP'.symm⟩
  rcases List.prefix_or_prefix_of_prefix h₁ h₂ with h | h
  · exact Or.inl fun i hi hai => (hc' i hi).2 (h.subset ((hc i hi).1 hai))
  · exact Or.inr fun i hi hbi => (hc i hi).2 (h.subset ((hc' i hi).1 hbi))

omit [Finite V] in
theorem AtSide.disj {S : Row m} {C : List (Fin m)} {P P' : List E} (hPP' : ∀ e ∈ P, e ∉ P') {a b : Row m} (ha : AtSide N S C P a) (hb : AtSide N S C P' b) : ∀ i ∈ C, a i ≠ S i → b i = S i := by
  obtain ⟨c, d, hP, hc⟩ := ha
  obtain ⟨c', d', hP', hc'⟩ := hb
  intro i hi hai
  by_contra hbi
  have h₁ : N.site i ∈ P := by rw [hP]; exact List.mem_append_left _ ((hc i hi).1 hai)
  have h₂ : N.site i ∈ P' := by rw [hP']; exact List.mem_append_left _ ((hc' i hi).1 hbi)
  exact hPP' _ h₁ h₂

/-- **Theorem 3.2 of the source**, the arrangement that a gall gives: `candidate` accepts the row at the recombination node. The sides of the gall are the two chains, and the ends of the chains are the parents of the recombination node on `C` (Corollary 2.1, in the direction that holds), so the recombination is the one in `N`. -/
theorem candidate_of_gall (hG : IsGalledTree N) (hc₁ : N.Obeys .single) {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q) {C : List (Fin m)} {rows : List (Row m)} {s : Row m}
    (hCQ : ∀ i ∈ C, N.site i ∈ {e | e ∈ p ∨ e ∈ q}) (hsx : ∀ i ∈ C, s i = N.label x i)
    (hrows : ∀ r ∈ rows, ∃ y, ∀ i ∈ C, r i = N.label y i) (hfl : ∀ r ∈ rows, ∃ i ∈ C, r i ≠ N.ancestral i)
    (hcov : ∀ i ∈ C, ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ r i ≠ N.ancestral i) (hne : C ≠ []) : (candidate N.ancestral C rows s).1 = true := by
  have hroot : ∀ i, N.ancestral i = N.label N.root i := fun _ => rfl
  have hside : ∀ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) → AtSide N N.ancestral C p r ∨ AtSide N N.ancestral C q r := by
    rintro r ⟨hr, hrs⟩
    obtain ⟨y, hy⟩ := hrows r hr
    obtain ⟨v, hv, hyv⟩ := exists_mem_label_eq hG hc y
    have hrv : ∀ i ∈ C, r i = N.label v i := fun i hi => (hy i hi).trans (hyv i (hCQ i hi))
    rcases cycle_mem_cases hc hv with rfl | ⟨c, d, hp, hd, hcv⟩ | ⟨c, d, hq, hd, hcv⟩
    · exact absurd (fun i hi => (hrv i hi).trans (hsx i hi).symm) hrs
    · refine Or.inl ⟨c, d, hp, fun i hi => ?_⟩
      rw [hrv i hi, hroot]
      exact label_cut hG hc hp hd hcv (hCQ i hi)
    · refine Or.inr ⟨c, d, hq, fun i hi => ?_⟩
      rw [hrv i hi, hroot]
      exact label_cut hG hc.symm hq hd hcv (Or.symm (hCQ i hi))
  have hpq : ∀ e ∈ p, e ∉ q := fun e he => hc.notMem he
  have hqp : ∀ e ∈ q, e ∉ p := fun e he => hc.symm.notMem he
  obtain ⟨a, b, ha, hb, hab, hax, hbx⟩ := cycle_last_arcs hc
  -- the states of the parent at the end of a side
  have htop : ∀ {P P' : List E} {a : E}, N.IsCycleOn w x P P' → a ∈ P → N.tgt a = x → (∀ e ∈ P, e ∉ P') → (∀ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) → AtSide N N.ancestral C P r ∨ AtSide N N.ancestral C P' r) →
      ∀ i ∈ C, N.label (N.src a) i ≠ N.ancestral i ↔ ∃ r, (r ∈ rows ∧ ¬ ∀ i ∈ C, r i = s i) ∧ AtSide N N.ancestral C P r ∧ r i ≠ N.ancestral i := by
    intro P P' a hc' ha' hax' hPP' hside' i hi
    obtain ⟨P₀, a', hP₀, hpath, hlast⟩ := hc'.2.1.exists_last_arc hc'.ne_nil
    have haa : a' = a := path_eq_of_tgt_eq hc'.2.1 (by rw [hP₀]; simp) ha' (hlast.trans hax'.symm)
    subst haa
    have hsi : N.site i ∈ {e | e ∈ P ∨ e ∈ P'} := by
      have h₀ := hCQ i hi
      by_cases hmem : N.site i ∈ P
      · exact Or.inl hmem
      · have hrr := hcov i hi
        obtain ⟨r, hr, hri⟩ := hrr
        rcases hside' r hr with ⟨c, d, hd, hc''⟩ | ⟨c, d, hd, hc''⟩
        · exact absurd (by rw [hd]; exact List.mem_append_left _ ((hc'' i hi).1 hri)) hmem
        · exact Or.inr (by rw [hd]; exact List.mem_append_left _ ((hc'' i hi).1 hri))
    have hcut := label_cut hG hc' hP₀ (by simp) hpath hsi
    have hsa : N.site i ≠ a' := by
      obtain ⟨_, b', hb', -, -, -, hbx'⟩ := cycle_last_arcs hc'
      obtain ⟨a₂, b₂, ha₂, hb₂, hab₂, hax₂, hbx₂⟩ := cycle_last_arcs hc'
      have heq : a₂ = a' := path_eq_of_tgt_eq hc'.2.1 ha₂ ha' (hax₂.trans hax'.symm)
      subst heq
      exact site_ne_of_tgt_eq hab₂ (hax₂.trans hbx₂.symm) i
    rw [show N.label (N.src a') i ≠ N.ancestral i ↔ N.site i ∈ P₀ from hcut]
    constructor
    · intro hm
      obtain ⟨r, hr, hri⟩ := hcov i hi
      refine ⟨r, hr, ?_, hri⟩
      rcases hside' r hr with h' | ⟨c, d, hd, hc''⟩
      · exact h'
      · exfalso
        have h₁ : N.site i ∈ P := by rw [hP₀]; exact List.mem_append_left _ hm
        exact hPP' _ h₁ (by rw [hd]; exact List.mem_append_left _ ((hc'' i hi).1 hri))
    · rintro ⟨r, -, ⟨c, d, hd, hc''⟩, hri⟩
      have h₁ : N.site i ∈ P := by rw [hd]; exact List.mem_append_left _ ((hc'' i hi).1 hri)
      rw [hP₀] at h₁
      rcases List.mem_append.1 h₁ with h₂ | h₂
      · exact h₂
      · exact absurd (List.mem_singleton.1 h₂) hsa
  refine candidate_of_sides (SP := AtSide N N.ancestral C p) (SQ := AtSide N N.ancestral C q) (tP := N.label (N.src a)) (tQ := N.label (N.src b)) hne hside
    (fun _ _ h₁ h₂ => h₁.comparable h₂) (fun _ _ h₁ h₂ => h₁.comparable h₂) (fun _ _ h₁ h₂ => h₁.disj hpq h₂) (fun _ _ h₁ h₂ => h₁.disj hqp h₂) hfl hcov
    (htop hc ha hax hpq hside) (htop hc.symm hb hbx hqp fun r hr => (hside r hr).symm) ?_
  -- the recombination of `N`
  obtain ⟨e, f, hef, he, hf, L₀, hL₀⟩ := hc₁ x hc.1
  obtain ⟨n, hn, hn'⟩ := exists_point L₀
  refine ⟨n, hn, ?_⟩
  have hsplit : ∀ i ∈ C, s i = if i.val < n then N.label (N.src e) i else N.label (N.src f) i := by
    intro i hi
    rw [hsx i hi, hL₀ i]
    by_cases hin : i ∈ L₀
    · rw [ite_eq_left hin, ite_eq_left ((hn' i).1 hin)]
    · rw [ite_eq_right hin, ite_eq_right (fun h => hin ((hn' i).2 h))]
  rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (he.trans hax.symm) with rfl | rfl
  · rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hf.trans hax.symm) with rfl | rfl
    · exact absurd rfl hef
    · exact Or.inr hsplit
  · rcases eq_or_eq_of_tgt hab (hax.trans hbx.symm) (hf.trans hax.symm) with rfl | rfl
    · exact Or.inl hsplit
    · exact absurd rfl hef

/-- On a gall, an incompatibility needs a row with the states of the recombination node, and that node has a `1` at one of the two sites (the proof of Theorem 2.2 of the source). -/
theorem gall_row (hG : IsGalledTree N) {w x : V} {p q : List E} (hc : N.IsCycleOn w x p q) {L : Finset (Row m)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) {i j : Fin m} (hi : N.site i ∈ {e | e ∈ p ∨ e ∈ q})
    (hj : N.site j ∈ {e | e ∈ p ∨ e ∈ q}) (hij : Incompatible L i j) :
    (∃ ρ ∈ L, ∀ u, N.site u ∈ {e | e ∈ p ∨ e ∈ q} → ρ u = N.label x u) ∧ (N.label x i ≠ N.label N.root i ∨ N.label x j ≠ N.label N.root j) := by
  obtain ⟨kind, τ, hτ⟩ := exists_threshold_mem hG hc
  have hrow : ∀ r ∈ L, (∀ s ∈ {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}, r s = N.label x s) ∨ ∃ z, ∀ s ∈ {s | N.site s ∈ {e | e ∈ p ∨ e ∈ q}}, (r s ≠ N.label x s ↔ OnSide kind τ z s) := by
    intro r hr
    obtain ⟨y, rfl⟩ := hL r hr
    obtain ⟨v, hv, hyv⟩ := exists_mem_label_eq hG hc y
    rcases hτ v hv with rfl | ⟨z, hz⟩
    · exact Or.inl hyv
    · exact Or.inr ⟨z, fun s hs => by rw [hyv s hs]; exact hz s hs⟩
  refine ⟨exists_row_of_incompatible hrow hi hj hij, ?_⟩
  rcases hτ w (coalescent_mem hc) with hwx | ⟨z, hz⟩
  · exfalso
    subst hwx
    exact hc.ne_nil hc.2.1.eq_nil_of_self
  · rcases onSide_or_of_incompatible hrow hi hj hij z with h | h
    · refine Or.inl fun h' => (hz i hi).2 h ?_
      rw [label_coalescent hc hi, h']
    · refine Or.inr fun h' => (hz j hj).2 h ?_
      rw [label_coalescent hc hj, h']

/-- **Complete on a component**: a galled tree makes `candidate` accept a row of any list of one row for each sequence of the component off the ancestral one. -/
theorem exists_candidate_of_gall (hG : IsGalledTree N) (hc₁ : N.Obeys .single) (hD : N.Derives M.toFinset) (c : (incompatGraph (addRow M.toFinset N.ancestral)).ConnectedComponent) (hnt : c.supp.Nontrivial)
    {Cl : List (Fin m)} (hCl : ∀ i, i ∈ Cl ↔ i ∈ c.supp) {rows : List (Row m)} (h₁ : ∀ r ∈ rows, ∃ ρ ∈ M, ∀ i ∈ Cl, r i = ρ i) (h₂ : ∀ r ∈ rows, ¬ ∀ i ∈ Cl, r i = N.ancestral i)
    (h₃ : ∀ ρ ∈ M, (¬ ∀ i ∈ Cl, ρ i = N.ancestral i) → ∃ r ∈ rows, ∀ i ∈ Cl, r i = ρ i) : ∃ s ∈ rows, (candidate N.ancestral Cl rows s).1 = true := by
  have hL := labels_addRow hD
  obtain ⟨i₀, j₀, hi₀, hadj⟩ := Cent.exists_adj (⟨c, hnt⟩ : Cent _)
  have hj₀ : j₀ ∈ c.supp := (SimpleGraph.ConnectedComponent.eq.2 hadj.reachable).symm.trans hi₀
  obtain ⟨Q, hQ, hsi, hsj⟩ := exists_isCycle_of_incompatible N hL hadj
  have hκ : ∀ s ∈ c.supp, N.site s ∈ Q := fun s hs => theorem2_4 hG hQ hL hsi (SimpleGraph.ConnectedComponent.exact (hi₀.trans hs.symm))
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  obtain ⟨⟨ρ, hρ, hρx⟩, hflip⟩ := gall_row hG hc hL hsi hsj hadj
  have hρne : ¬ ∀ i ∈ Cl, ρ i = N.ancestral i := by
    intro h
    rcases hflip with h' | h'
    · exact h' ((hρx i₀ hsi).symm.trans (h i₀ ((hCl i₀).2 hi₀)))
    · exact h' ((hρx j₀ hsj).symm.trans (h j₀ ((hCl j₀).2 hj₀)))
  have hLM : ∀ {r : Row m}, r ∈ addRow M.toFinset N.ancestral → (∃ i ∈ Cl, r i ≠ N.ancestral i) → r ∈ M := by
    rintro r hr ⟨i, -, hi⟩
    rcases mem_addRow.1 hr with rfl | hr
    · exact absurd rfl hi
    · exact List.mem_toFinset.1 hr
  have hρM : ρ ∈ M := by
    refine hLM hρ ?_
    by_contra hno
    push Not at hno
    exact hρne hno
  obtain ⟨s, hs, hse⟩ := h₃ ρ hρM hρne
  refine ⟨s, hs, candidate_of_gall hG hc₁ hc (fun i hi => hκ i ((hCl i).1 hi)) (fun i hi => (hse i hi).trans (hρx i (hκ i ((hCl i).1 hi)))) (fun r hr => ?_) (fun r hr => ?_) (fun i hi => ?_) ?_⟩
  · obtain ⟨ρ', hρ', hre⟩ := h₁ r hr
    obtain ⟨y, rfl⟩ := hD.displays ρ' (List.mem_toFinset.2 hρ')
    exact ⟨y, hre⟩
  · have := h₂ r hr
    by_contra hno
    push Not at hno
    exact this hno
  · obtain ⟨k, hk⟩ := exists_incompatible_of_nontrivial hnt ((hCl i).1 hi)
    have hkC : k ∈ Cl := (hCl k).2 ((SimpleGraph.ConnectedComponent.eq.2 (SimpleGraph.Adj.reachable (G := incompatGraph _) hk)).symm.trans ((hCl i).1 hi))
    have hne : (!N.ancestral i) ≠ N.ancestral i := by cases N.ancestral i <;> simp
    obtain ⟨r, hr, hr₁, hr₂⟩ : ∃ r ∈ addRow M.toFinset N.ancestral, r i = !N.ancestral i ∧ r k ≠ s k := by
      cases hsk : s k
      · obtain ⟨r, hr, h₁, h₂⟩ := hk (!N.ancestral i) true
        exact ⟨r, hr, h₁, by rw [h₂]; simp⟩
      · obtain ⟨r, hr, h₁, h₂⟩ := hk (!N.ancestral i) false
        exact ⟨r, hr, h₁, by rw [h₂]; simp⟩
    have hrf : r i ≠ N.ancestral i := by rw [hr₁]; exact hne
    have hrM : r ∈ M := hLM hr ⟨i, hi, hrf⟩
    obtain ⟨r', hr', hre⟩ := h₃ r hrM fun h => hrf (h i hi)
    refine ⟨r', ⟨hr', fun h => hr₂ ((hre k hkC).symm.trans (h k hkC))⟩, ?_⟩
    rw [hre i hi]
    exact hrf
  · intro h
    have : i₀ ∈ Cl := (hCl i₀).2 hi₀
    rw [h] at this
    simp at this

/-- **Complete on a component**: a galled tree makes the Site-Arrangement Algorithm accept. -/
theorem compTest_of_gall (hG : IsGalledTree N) (hc₁ : N.Obeys .single) (hD : N.Derives M.toFinset) (c : (incompatGraph (addRow M.toFinset N.ancestral)).ConnectedComponent) (hnt : c.supp.Nontrivial)
    {Cl : List (Fin m)} (hCl : ∀ i, i ∈ Cl ↔ i ∈ c.supp) : (compTest N.ancestral M Cl).1 = true := by
  have hnzM : ∀ {r : Row m}, r ∈ (filterOps M fun r => (!(eqOn Cl r N.ancestral).1, (eqOn Cl r N.ancestral).2)).1 → r ∈ M ∧ ¬ ∀ i ∈ Cl, r i = N.ancestral i := by
    intro r hr
    obtain ⟨h₁, h₂⟩ := List.mem_filter.1 hr
    refine ⟨h₁, fun h₃ => ?_⟩
    have := eqOn_iff.2 h₃
    simp [this] at h₂
  have hnz : ∀ {r : Row m}, r ∈ M → (¬ ∀ i ∈ Cl, r i = N.ancestral i) → r ∈ (filterOps M fun r => (!(eqOn Cl r N.ancestral).1, (eqOn Cl r N.ancestral).2)).1 := by
    intro r hr hne
    refine List.mem_filter.2 ⟨hr, ?_⟩
    have : ¬ (eqOn Cl r N.ancestral).1 = true := fun h' => hne (eqOn_iff.1 h')
    simpa using this
  simp only [compTest, anyOps, List.any_eq_true]
  exact exists_candidate_of_gall hG hc₁ hD c hnt hCl (fun r hr => ⟨r, (hnzM (mem_of_mem_distinctOn hr)).1, fun _ _ => rfl⟩) (fun r hr => (hnzM (mem_of_mem_distinctOn hr)).2)
    fun ρ hρ hne => exists_mem_distinctOn (hnz hρ hne)

end Complete

/-! ### The decision -/

section Decide

open scoped Classical

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

/-- The labels of `labOf` on the edges of the test are the components of the conflict graph. -/
theorem lab_iff (k l : Fin m) : labOf (edgesOps S M).1 k = labOf (edgesOps S M).1 l ↔ (incompatGraph (addRow M.toFinset S)).Reachable k l := by
  rw [← conflictGraph_eq_incompatGraph_addRow]
  refine labOf_iff (fun e he => ?_) (fun i j h => (edgesOps_spec i j).2 h) k l
  obtain ⟨i, j⟩ := e
  exact (edgesOps_spec i j).1 he

/-- The sites with one label are the component. -/
theorem mem_filter_lab (k₀ i : Fin m) : i ∈ (List.finRange m).filter (fun k => decide (labOf (edgesOps S M).1 k = labOf (edgesOps S M).1 k₀)) ↔ i ∈ ((incompatGraph (addRow M.toFinset S)).connectedComponentMk k₀).supp := by
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, lab_iff]
  exact (SimpleGraph.ConnectedComponent.eq (G := incompatGraph (addRow M.toFinset S))).symm

/-- A component has more than one site exactly when it is non-trivial. -/
theorem one_lt_length_iff (k₀ : Fin m) : 1 < ((List.finRange m).filter (fun k => decide (labOf (edgesOps S M).1 k = labOf (edgesOps S M).1 k₀))).length ↔ ((incompatGraph (addRow M.toFinset S)).connectedComponentMk k₀).supp.Nontrivial := by
  have hnd := (List.nodup_finRange m).filter (fun k => decide (labOf (edgesOps S M).1 k = labOf (edgesOps S M).1 k₀))
  rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨a, (mem_filter_lab k₀ a).1 (List.mem_toFinset.1 ha), b, (mem_filter_lab k₀ b).1 (List.mem_toFinset.1 hb), hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, b, List.mem_toFinset.2 ((mem_filter_lab k₀ a).2 ha), List.mem_toFinset.2 ((mem_filter_lab k₀ b).2 hb), hab⟩

/-- **The decision is sound, with a reduced galled tree.** If `galledDecide` says `true`, there is a reduced galled tree for `M` with ancestral sequence `S` and single crossovers. The hypotheses are the source's: there are rows, and each column has a `1`. -/
theorem exists_reduced_of_decide (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) (h : (galledDecide S M).1 = true) :
    ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives M.toFinset ∧ N.ancestral = S ∧ IsReducedGalledTree N (conflictGraph S M.toFinset) := by
  rw [conflictGraph_eq_incompatGraph_addRow]
  have hS : S ∈ addRow M.toFinset S := mem_addRow.2 (Or.inl rfl)
  have hC' : NoConstantColumn (addRow M.toFinset S) := fun i => by
    obtain ⟨r, hr, hri⟩ := h1 i
    exact ⟨r, mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr)), S, hS, hri⟩
  by_cases hne : ∃ r ∈ addRow M.toFinset S, r ≠ S
  · have hpiece : ∀ C : Cent (incompatGraph (addRow M.toFinset S)), ∃ (a b : ℕ) (P : Network C.1.supp (Fin a) (Fin b)), P.Obeys .single ∧ P.ancestral = C.1.supp.domRestrict S ∧ P.Derives ((restrictRows C.1.supp (addRow M.toFinset S)).erase (C.1.supp.domRestrict S)) ∧ P.recombCount ≤ 1 := by
      rintro ⟨c, hnt⟩
      obtain ⟨k₀, rfl⟩ := c.exists_rep
      have hall : ∀ c₀ ∈ ((List.finRange m).map (labOf (edgesOps S M).1)).dedup, (labelTest S M (labOf (edgesOps S M).1) c₀).1 = true := by
        simpa [galledDecide, allOps] using h
      have ht := hall _ (List.mem_dedup.2 (List.mem_map.2 ⟨k₀, List.mem_finRange k₀, rfl⟩))
      have hlen := (one_lt_length_iff (S := S) (M := M) k₀).2 hnt
      have hnot : ¬ ((List.finRange m).filter (fun k => decide (labOf (edgesOps S M).1 k = labOf (edgesOps S M).1 k₀))).length ≤ 1 := by omega
      simp only [labelTest, hnot, ite_false] at ht
      exact exists_piece_of_compTest _ (mem_filter_lab k₀) ht
    choose a b P hob hanc hder hrec using hpiece
    exact exists_reduced_of_pieces .single hC' hne P hob hanc (fun C => by convert hder C) hrec
  · push Not at hne
    have hι : IsEmpty (Fin m) := ⟨fun i => by
      obtain ⟨r, hr, hri⟩ := h1 i
      exact hri (by rw [hne r (mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr)))])⟩
    have hMne : M.toFinset.Nonempty := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil M hM
      exact ⟨r, List.mem_toFinset.2 hr⟩
    obtain ⟨a', b', N', hr, hd, hs, -⟩ := Gusfield1991.exists_network_of_no_conflict M.toFinset S hMne hC' (fun i => hι.elim i)
    have hinj := Network.tgt_injective_of_no_recomb hr
    have hcyc : ∀ Q, ¬ N'.IsCycle Q := Network.not_isCycle_of_tgt_injective hinj
    exact ⟨a', b', N', Network.obeys_of_tgt_injective hinj _, hd, hs, fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q)⟩

/-- **The decision** (`ext:galled_decide`), Sections 3.1, 3.2 and 7 of the source, and Theorem 3.2. `galledDecide S M` says `true` exactly when there is a galled tree for `M` with ancestral sequence `S` and single crossovers. The hypotheses are the source's standing assumptions that there are rows and that each column has a `1`.

Departure from the source: Section 7 decides by running the whole algorithm, Sections 3 to 6, and checking the galled tree it built. Here the decision needs only the arrangement of each component, and the gluing of Theorem 1 of Gusfield et al. 2007 shows that those arrangements fit together: so the decision doesn't build the part of the network outside the galls. -/
theorem galledDecide_iff (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) :
    (galledDecide S M).1 = true ↔ ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), IsGalledTree N ∧ N.Obeys .single ∧ N.Derives M.toFinset ∧ N.ancestral = S := by
  constructor
  · intro h
    obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := exists_reduced_of_decide hM h1 h
    exact ⟨a, b, N, h₄.galled, h₁, h₂, h₃⟩
  · rintro ⟨a, b, N, hG, hc₁, hD, rfl⟩
    simp only [galledDecide, allOps, List.all_eq_true]
    intro c₀ hc₀
    obtain ⟨k₀, -, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hc₀)
    unfold labelTest
    dsimp only
    split_ifs with hlen
    · rfl
    · have hnt := (one_lt_length_iff (S := N.ancestral) (M := M) k₀).1 (by omega)
      exact compTest_of_gall hG hc₁ hD _ hnt (mem_filter_lab k₀)

/-! ### The count of the decision -/

theorem conflictOps_le (S : Row m) (M : List (Row m)) (i j : Fin m) : (conflictOps S M i j).2 ≤ 6 * M.length := by
  have h : ∀ a b, (hasPair M i j a b).2 ≤ M.length * 2 := fun a b => anyOps_le fun _ _ => le_rfl
  have h₁ := h (!S i) (!S j)
  have h₂ := h (!S i) (S j)
  have h₃ := h (S i) (!S j)
  simp only [conflictOps]
  omega

theorem compTest_le (S : Row m) (M : List (Row m)) {C : List (Fin m)} (hC : C.length ≤ m) :
    (compTest S M C).2 ≤ M.length * m + M.length * (M.length * m) +
      M.length * (7 * (M.length * M.length * m) + 4 * (M.length * m) + 3 * (M.length * m) + (m + 1) * (2 * (m * (2 * M.length + 1))) + M.length * m + m * (2 * M.length)) := by
  have hmul : ∀ {x y : ℕ}, x ≤ y → x * C.length ≤ y * m := fun h => Nat.mul_le_mul h hC
  have h₁ : (filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)).2 ≤ M.length * m := (filterOps_le (c := C.length) fun b _ => eqOn_le C b S).trans (hmul le_rfl)
  have hnz : (filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)).1.length ≤ M.length := filterOps_length_le
  have h₂ : (distinctOn C (filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)).1).2 ≤ M.length * (M.length * m) :=
    (distinctOn_le C _).trans (Nat.mul_le_mul hnz (hmul hnz))
  have hrows : (distinctOn C (filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)).1).1.length ≤ M.length := (distinctOn_length_le C _).trans hnz
  have h₃ := anyOps_le (l := (distinctOn C (filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)).1).1) (p := candidate S C (distinctOn C (filterOps M fun r => (!(eqOn C r S).1, (eqOn C r S).2)).1).1) fun s _ => candidate_le S hC _ s hrows
  have h₄ := h₃.trans (Nat.mul_le_mul_right _ hrows)
  simp only [compTest]
  omega

/-- **The count of the decision** (`ext:galled_ops`): on `n` rows and `m` sites, `galledDecide` makes at most `51 (n + m + 1)⁵` operations, an operation being a read of an entry, a comparison of two states, or a write of a label.

This is a bound in `n` and `m`, and not the source's `O(nm + n³)`. The function tests a perfect phylogeny by comparing all the pairs of rows, where the source cites an `O(n |C|)` algorithm, and it isn't tuned. So `m ≤ 2n`, which the source cites from Wang et al. 2001 for its form, isn't needed here, and isn't proved. -/
theorem galledDecide_ops_le (S : Row m) (M : List (Row m)) : (galledDecide S M).2 ≤ 51 * (M.length + m + 1) ^ 5 := by
  obtain ⟨n, hn⟩ : ∃ n, n = M.length := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = n + m + 1 := ⟨_, rfl⟩
  rw [← hn, ← hX]
  have hnX : n ≤ X := by omega
  have hmX : m ≤ X := by omega
  have h1X : 1 ≤ X := by omega
  have hp : ∀ {a b : ℕ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Nat.pow_le_pow_right h1X h
  have h₃ : n * n * m ≤ X ^ 3 := by
    calc n * n * m ≤ X * X * X := by gcongr
      _ = X ^ 3 := by ring
  have h₂ : n * m ≤ X ^ 2 := by
    calc n * m ≤ X * X := by gcongr
      _ = X ^ 2 := by ring
  have h₂' : m * m ≤ X ^ 2 := by
    calc m * m ≤ X * X := by gcongr
      _ = X ^ 2 := by ring
  have h₄ : (m + 1) * (2 * (m * (2 * n + 1))) ≤ 12 * X ^ 3 := by
    calc (m + 1) * (2 * (m * (2 * n + 1))) ≤ (2 * X) * (2 * (X * (3 * X))) := by
          have h₅ : m + 1 ≤ 2 * X := by omega
          have h₆ : 2 * n + 1 ≤ 3 * X := by omega
          gcongr
      _ = 12 * X ^ 3 := by ring
  have h₅ : m * (2 * n) = 2 * (n * m) := by ring
  have hcand : 7 * (n * n * m) + 4 * (n * m) + 3 * (n * m) + (m + 1) * (2 * (m * (2 * n + 1))) + n * m + m * (2 * n) ≤ 29 * X ^ 3 := by
    have := hp (show 2 ≤ 3 by omega)
    omega
  have hcomp : ∀ {C : List (Fin m)}, C.length ≤ m → (compTest S M C).2 ≤ 41 * X ^ 4 := by
    intro C hC
    have h₆ := compTest_le S M hC
    rw [← hn] at h₆
    have h₇ : n * (7 * (n * n * m) + 4 * (n * m) + 3 * (n * m) + (m + 1) * (2 * (m * (2 * n + 1))) + n * m + m * (2 * n)) ≤ 29 * X ^ 4 := by
      calc _ ≤ X * (29 * X ^ 3) := Nat.mul_le_mul hnX hcand
        _ = 29 * X ^ 4 := by ring
    have h₈ : n * (n * m) ≤ X ^ 3 := by
      calc n * (n * m) ≤ X * (X * X) := by gcongr
        _ = X ^ 3 := by ring
    have h₉ := hp (show 3 ≤ 4 by omega)
    have h₁₀ := hp (show 2 ≤ 4 by omega)
    omega
  have hlabel : ∀ (f : Fin m → Fin m) (c : Fin m), (labelTest S M f c).2 ≤ 42 * X ^ 4 := by
    intro f c
    have hlen : ((List.finRange m).filter fun k => decide (f k = c)).length ≤ m := (List.length_filter_le _ _).trans (by simp)
    have h₆ := hcomp hlen
    have h₇ : X ^ 1 ≤ X ^ 4 := hp (by omega)
    have h₈ : m ≤ X ^ 4 := hmX.trans (by simpa using h₇)
    unfold labelTest
    dsimp only
    split_ifs
    · dsimp only
      omega
    · dsimp only
      omega
  have hconf : ∀ e : Fin m × Fin m, (conflictOps S M e.1 e.2).2 ≤ 6 * n := fun e => by
    rw [hn]
    exact conflictOps_le S M e.1 e.2
  have hlen : ((List.finRange m).product (List.finRange m)).length = m * m := by
    change (List.finRange m ×ˢ List.finRange m).length = m * m
    rw [List.length_product, List.length_finRange]
  have hes : (edgesOps S M).2 ≤ m * m * (6 * n) := by
    have := filterOps_le (l := (List.finRange m).product (List.finRange m)) (p := fun e => conflictOps S M e.1 e.2) (c := 6 * n) fun e _ => hconf e
    rw [hlen] at this
    exact this
  have hesL : (edgesOps S M).1.length ≤ m * m := by
    have : (edgesOps S M).1.length ≤ ((List.finRange m).product (List.finRange m)).length := filterOps_length_le
    rwa [hlen] at this
  have hrepsL : ∀ f : Fin m → Fin m, ((List.finRange m).map f).dedup.length ≤ m := fun f => by
    have h₆ := List.Sublist.length_le (List.dedup_sublist ((List.finRange m).map f))
    simpa using h₆
  simp only [galledDecide]
  have ht := allOps_le (l := ((List.finRange m).map (labOf (edgesOps S M).1)).dedup) (p := labelTest S M (labOf (edgesOps S M).1)) (c := 42 * X ^ 4) fun c _ => hlabel _ c
  have ht' : (allOps ((List.finRange m).map (labOf (edgesOps S M).1)).dedup (labelTest S M (labOf (edgesOps S M).1))).2 ≤ 42 * X ^ 5 := by
    calc _ ≤ _ := ht
      _ ≤ X * (42 * X ^ 4) := Nat.mul_le_mul_right _ ((hrepsL _).trans hmX)
      _ = 42 * X ^ 5 := by ring
  have h₆ : m * m * (6 * n) ≤ 6 * X ^ 3 := by
    calc m * m * (6 * n) ≤ X * X * (6 * X) := by gcongr
      _ = 6 * X ^ 3 := by ring
  have h₇ : m * (edgesOps S M).1.length ≤ X ^ 3 := by
    calc m * (edgesOps S M).1.length ≤ X * (X * X) := Nat.mul_le_mul hmX (hesL.trans (Nat.mul_le_mul hmX hmX))
      _ = X ^ 3 := by ring
  have h₈ := hp (show 3 ≤ 5 by omega)
  have h₉ := hp (show 2 ≤ 5 by omega)
  omega

end Decide

end GusfieldEtAl2004.Algorithm
