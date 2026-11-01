module

public import Gusfield2007.Histories
public import Batteries.Data.Nat.Lemmas

/-!
# Gusfield et al. 2007: a verified search for lower bounds on `R`

Lower bounds on `R`, in the kernel. It isn't in the paper, which obtains its numbers from programs (beagle, multicross.pl; lines 404, 612).

If a network for `M` has at most `b` recombination nodes, then by `Gen.card_le` its labels, with the intermediate ones of the arcs with several sites, are a set `L` of at most `1 + m + b` sequences,
containing `M` and the root. By `Gen.mem_of_closed`, the root generates all of `L` inside `L`, by changing one site and by recombining two sequences, with no regard to the sites used or
the number of recombinations. So we go through the possible roots and the possible extra sequences of `L`, and for each one we compute what the root generates inside `L`. If a row of `M` is never
generated, then that `L` isn't possible. When `M` is large with respect to `1 + m + b`, there are few possible `L`, and the search is short; for all the figures of the paper it's a matter of seconds.

A sequence is coded by the number with its bits (`code`), and the search `check` is a computation on numbers, for the kernel: `Nat.xor`, `Nat.land`, `Nat.beq` are fast there. The result `LabelSearch.lt_of_check` is for
histories in the model `multiple`, and so for all models. The search is about `multiple`, and for `single` the bound can be better: see `Gen.split`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

namespace LabelSearch

/-- Membership in a list of numbers, for the kernel. -/
def memN (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: l => Nat.beq x y || memN x l

/-- The numbers differ in exactly one bit. -/
def oneStep (x y : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.xor x y) (Nat.xor x y - 1)) 0 && !Nat.beq (Nat.xor x y) 0

/-- Each bit of `q` is the bit of `p` or the bit of `p'`. -/
def isMix (q p p' : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.xor q p) (Nat.xor q p')) 0

/-- `r` is one step from `X`. -/
def derivable (X : List ℕ) (r : ℕ) : Bool :=
  X.any fun p => oneStep r p || X.any fun p' => isMix r p p'

/-- Add to `X` what can be generated from it inside `X ∪ rest`, until nothing changes, and then say whether all of `Mc` is in `X`. Out of fuel, it answers `true`, "can't exclude". -/
def covers (Mc : List ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, X, rest =>
    match rest.filter (derivable X) with
    | [] => Mc.all (memN · X)
    | a :: new => covers Mc fuel (a :: new ++ X) (rest.filter fun r => !derivable X r)

/-- Is there a set of labels `L`, with at most `k` sequences more than `L₀`, whose root `S` generates all of `Mc` inside `L`? -/
def good (Mc U : List ℕ) (S : ℕ) : ℕ → List ℕ → Bool
  | 0, L => covers Mc (L.length + 1) [S] (L.filter fun r => !Nat.beq r S)
  | k + 1, L => covers Mc (L.length + 1) [S] (L.filter fun r => !Nat.beq r S) ||
      U.any fun z => !memN z L && good Mc U S k (z :: L)

/-- `good` for the root `S`, with at most `cap` labels. -/
def checkRoot (m : ℕ) (Mc : List ℕ) (cap S : ℕ) : Bool :=
  bif memN S Mc then Nat.ble Mc.length cap && good Mc (List.range (2 ^ m)) S (cap - Mc.length) Mc
  else bif Nat.ble (Mc.length + 1) cap then good Mc (List.range (2 ^ m)) S (cap - Mc.length - 1) (S :: Mc) else false

/-- Is there a possible root and set of labels, with at most `1 + m + b` labels, for the rows `Mc`? If this is `false`, then `Mc` needs more than `b` recombinations. -/
def check (m : ℕ) (Mc : List ℕ) (b : ℕ) : Bool :=
  (List.range (2 ^ m)).any (checkRoot m Mc (1 + m + b))

/-- The sequence with the bits of a number. -/
def dec {m : ℕ} (x : ℕ) : Fin m → Bool := fun i => x.testBit i

/-- The number with the bits of a sequence. -/
def code {m : ℕ} (r : Fin m → Bool) : ℕ := Nat.ofBits r

theorem memN_iff {x : ℕ} {l : List ℕ} : memN x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memN]
  | cons y l ih =>
    simp [memN, ih]

theorem memN_eq_false_iff {x : ℕ} {l : List ℕ} : memN x l = false ↔ x ∉ l := by
  rw [← memN_iff, Bool.not_eq_true]

theorem beq_eq_false_of_ne {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  rw [← Bool.not_eq_true]
  exact fun h' => h (Nat.eq_of_beq_eq_true h')

section Code

variable {m : ℕ}

theorem testBit_code (r : Fin m → Bool) (i : Fin m) : (code r).testBit i = r i :=
  Nat.testBit_ofBits_lt r i i.2

theorem testBit_code_of_le (r : Fin m → Bool) {j : ℕ} (h : m ≤ j) : (code r).testBit j = false :=
  Nat.testBit_ofBits_ge r j h

theorem code_lt (r : Fin m → Bool) : code r < 2 ^ m :=
  Nat.ofBits_lt_two_pow r

theorem code_dec {x : ℕ} (hx : x < 2 ^ m) : code (dec x : Fin m → Bool) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < m
  · exact testBit_code _ ⟨j, hj⟩
  · rw [testBit_code_of_le _ (not_lt.1 hj), Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (not_lt.1 hj)))]

theorem dec_code (r : Fin m → Bool) : (dec (code r) : Fin m → Bool) = r := by
  funext i
  exact testBit_code r i

theorem oneStep_of_isFlip {i : Fin m} {p q : Fin m → Bool} (h : IsFlip i p q) : oneStep (code q) (code p) = true := by
  have hx : Nat.xor (code q) (code p) = 2 ^ i.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    change ((code q) ^^^ (code p)).testBit j = _
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
  have h₀ : Nat.land (2 ^ i.val) (2 ^ i.val - 1) = 0 := by
    change (2 ^ i.val) &&& (2 ^ i.val - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  unfold oneStep
  rw [hx, h₀, beq_eq_false_of_ne (Nat.two_pow_pos i.val).ne']
  rfl

theorem isMix_of_isMix {p p' q : Fin m → Bool} (h : Recombinant .multiple p p' q) : isMix (code q) (code p) (code p') = true := by
  have hx : Nat.land (Nat.xor (code q) (code p)) (Nat.xor (code q) (code p')) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    change (((code q) ^^^ (code p)) &&& ((code q) ^^^ (code p'))).testBit j = _
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.zero_testBit]
    by_cases hj : j < m
    · have h₁ := testBit_code q ⟨j, hj⟩
      have h₂ := testBit_code p ⟨j, hj⟩
      have h₃ := testBit_code p' ⟨j, hj⟩
      simp only at h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      rcases h ⟨j, hj⟩ with h' | h' <;> rw [h'] <;> simp
    · rw [testBit_code_of_le q (not_lt.1 hj), testBit_code_of_le p (not_lt.1 hj), testBit_code_of_le p' (not_lt.1 hj)]
      rfl
  unfold isMix
  rw [hx]
  rfl

end Code

/-- What `covers` finds when it answers `false`: a closed set of numbers that misses a row. -/
theorem covers_eq_false {Mc : List ℕ} : ∀ (fuel : ℕ) (X rest : List ℕ), covers Mc fuel X rest = false →
    ∃ X' : List ℕ, (∀ x ∈ X, x ∈ X') ∧ (∀ x ∈ X', x ∈ X ∨ x ∈ rest) ∧ (∀ r ∈ rest, r ∉ X' → derivable X' r = false) ∧
      ∃ x ∈ Mc, x ∉ X' := by
  intro fuel
  induction fuel with
  | zero =>
    intro X rest h
    simp [covers] at h
  | succ fuel ih =>
    intro X rest h
    rw [covers] at h
    split at h
    · rename_i hnil
      refine ⟨X, fun _ hx => hx, fun _ hx => Or.inl hx, fun r hr _ => ?_, ?_⟩
      · rw [List.filter_eq_nil_iff] at hnil
        simpa using hnil r hr
      · rw [List.all_eq_false] at h
        obtain ⟨x, hx, hx'⟩ := h
        refine ⟨x, hx, ?_⟩
        rw [← memN_iff]
        simpa using hx'
    · rename_i a new hnew
      obtain ⟨X', h₁, h₂, h₃, h₄⟩ := ih _ _ h
      have hsub : ∀ x ∈ a :: new, x ∈ rest ∧ derivable X x = true := fun x hx => by
        rw [← hnew, List.mem_filter] at hx
        exact hx
      refine ⟨X', fun x hx => h₁ x (by simp [hx]), fun x hx => ?_, fun r hr hrX => ?_, h₄⟩
      · rcases h₂ x hx with hx' | hx'
        · rw [List.cons_append, List.mem_cons, List.mem_append] at hx'
          rcases hx' with rfl | hx' | hx'
          · exact Or.inr (hsub _ (List.mem_cons_self ..)).1
          · exact Or.inr (hsub _ (List.mem_cons_of_mem _ hx')).1
          · exact Or.inl hx'
        · exact Or.inr (List.mem_filter.1 hx').1
      · refine h₃ r (List.mem_filter.2 ⟨hr, ?_⟩) hrX
        by_contra hd
        have hd' : derivable X r = true := by simpa using hd
        have : r ∈ a :: new := by
          rw [← hnew]
          exact List.mem_filter.2 ⟨hr, hd'⟩
        exact hrX (h₁ r (List.mem_append_left X this))

section Sound

variable {m : ℕ} {S : Fin m → Bool} {A : Finset (Fin m → Bool)} {U : Set (Fin m)} {r : ℕ} {Mc : List ℕ}

theorem covers_of_gen (h : Gen .multiple S A U r) (hMc : ∀ x ∈ Mc, ∃ a ∈ A, code a = x) {fuel : ℕ} {X rest : List ℕ}
    (hS : code S ∈ X) (hA : ∀ a ∈ A, code a ∈ X ∨ code a ∈ rest) : covers Mc fuel X rest = true := by
  by_contra hne
  obtain ⟨X', h₁, h₂, h₃, x, hx, hxX⟩ := covers_eq_false _ _ _ (by simpa using hne)
  have hstep : ∀ q ∈ A, derivable X' (code q) = true → code q ∈ X' := fun q hq hd => by
    by_contra hqX
    rcases hA q hq with hq' | hq'
    · exact hqX (h₁ _ hq')
    · rw [h₃ _ hq' hqX] at hd
      exact absurd hd (by simp)
  have hclosed : ∀ a ∈ A, a ∈ {a | code a ∈ X'} := h.mem_of_closed (Y := A) subset_rfl (h₁ _ hS)
    (fun i p q hp hq hf => hstep q hq (List.any_eq_true.2 ⟨code p, hp, by rw [oneStep_of_isFlip hf]; rfl⟩))
    (fun p p' q hp hp' hq hm => hstep q hq (List.any_eq_true.2 ⟨code p, hp, by
      rw [Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.2 ⟨code p', hp', isMix_of_isMix hm⟩)⟩))
  obtain ⟨a, ha, rfl⟩ := hMc x hx
  exact hxX (hclosed a ha)

theorem good_of_gen (h : Gen .multiple S A U r) (hMc : ∀ x ∈ Mc, ∃ a ∈ A, code a = x) (k : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, ∃ a ∈ A, code a = x)
    (hk : (A.filter fun a => code a ∉ L).card ≤ k) : good Mc (List.range (2 ^ m)) (code S) k L = true := by
  induction k generalizing L with
  | zero =>
    rw [good]
    refine covers_of_gen h hMc (List.mem_singleton.2 rfl) fun a ha => ?_
    have hmem : code a ∈ L := by
      by_contra hna
      have : 0 < (A.filter fun a => code a ∉ L).card := Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha, hna⟩⟩
      omega
    by_cases hS : code a = code S
    · exact Or.inl (List.mem_singleton.2 hS)
    · exact Or.inr (List.mem_filter.2 ⟨hmem, by rw [beq_eq_false_of_ne hS]; rfl⟩)
  | succ k ih =>
    rw [good, Bool.or_eq_true]
    by_cases hall : ∀ a ∈ A, code a ∈ L
    · refine Or.inl (covers_of_gen h hMc (List.mem_singleton.2 rfl) fun a ha => ?_)
      by_cases hS : code a = code S
      · exact Or.inl (List.mem_singleton.2 hS)
      · exact Or.inr (List.mem_filter.2 ⟨hall a ha, by rw [beq_eq_false_of_ne hS]; rfl⟩)
    · push Not at hall
      obtain ⟨a, ha, haL⟩ := hall
      refine Or.inr (List.any_eq_true.2 ⟨code a, List.mem_range.2 (code_lt a), ?_⟩)
      rw [Bool.and_eq_true]
      refine ⟨by simpa using memN_eq_false_iff.2 haL, ih (code a :: L) ?_ ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨a, ha, rfl⟩
        · exact hL x hx
      · have hsub : (A.filter fun a' => code a' ∉ code a :: L) ⊆ (A.filter fun a' => code a' ∉ L).erase a := by
          intro a' ha'
          rw [Finset.mem_filter, List.mem_cons, not_or] at ha'
          refine Finset.mem_erase.2 ⟨fun heq => ha'.2.1 (by rw [heq]), Finset.mem_filter.2 ⟨ha'.1, ha'.2.2⟩⟩
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨ha, haL⟩)] at hcard
        omega

/-- The sequences of `A` outside `L` are at most what `A` has more than `L`. -/
theorem card_filter_notMem_le {cap : ℕ} (hA : A.card ≤ cap) {L : List ℕ} (hnd : L.Nodup) (hL : ∀ x ∈ L, ∃ a ∈ A, code a = x) :
    L.length ≤ A.card ∧ (A.filter fun a => code a ∉ L).card ≤ cap - L.length := by
  have hsub : L.toFinset ⊆ (A.filter fun a => code a ∈ L).image code := fun x hx => by
    obtain ⟨a, ha, rfl⟩ := hL x (List.mem_toFinset.1 hx)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨ha, List.mem_toFinset.1 hx⟩)
  have h₁ := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at h₁
  have h₂ := Finset.card_image_le (s := A.filter fun a => code a ∈ L) (f := code)
  have h₃ := Finset.card_filter_add_card_filter_not (s := A) (fun a => code a ∈ L)
  omega

/-- **The soundness of the search.** If `check` says `false`, a multiple-crossover history whose labels contain the rows has more than `b` recombinations. -/
theorem lt_of_check {b : ℕ} (hnd : Mc.Nodup) (hcheck : check m Mc b = false) (h : Gen .multiple S A U r)
    (hMc : ∀ x ∈ Mc, ∃ a ∈ A, code a = x) : b < r := by
  by_contra hr
  have hA : A.card ≤ 1 + m + b := by
    have h₁ := h.card_le
    have h₂ : U.ncard ≤ m := by
      have := Set.ncard_le_ncard (Set.subset_univ U)
      simpa [Set.ncard_univ] using this
    omega
  have hroot : checkRoot m Mc (1 + m + b) (code S) = true := by
    rw [checkRoot]
    by_cases hS : code S ∈ Mc
    · rw [memN_iff.2 hS, Bool.cond_true]
      obtain ⟨h₁, h₂⟩ := card_filter_notMem_le hA hnd hMc
      rw [Bool.and_eq_true, Nat.ble_eq]
      exact ⟨by omega, good_of_gen h hMc _ _ hMc h₂⟩
    · rw [memN_eq_false_iff.2 hS, Bool.cond_false]
      have hL : ∀ x ∈ code S :: Mc, ∃ a ∈ A, code a = x := fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨S, h.root_mem, rfl⟩
        · exact hMc x hx
      obtain ⟨h₁, h₂⟩ := card_filter_notMem_le hA (List.nodup_cons.2 ⟨hS, hnd⟩) hL
      have hble : Nat.ble (Mc.length + 1) (1 + m + b) = true := by
        rw [Nat.ble_eq]
        simp only [List.length_cons] at h₁
        omega
      rw [hble, Bool.cond_true]
      refine good_of_gen h hMc _ _ hL ?_
      simp only [List.length_cons] at h₂
      omega
  have : check m Mc b = true := List.any_eq_true.2 ⟨code S, List.mem_range.2 (code_lt S), hroot⟩
  rw [this] at hcheck
  exact absurd hcheck (by simp)

end Sound

end LabelSearch

open LabelSearch

/-! ### Lower bounds on the number of recombination nodes -/

section Bound

variable {m : ℕ}

/-- The rows of `M`, coded: `Mc` are codes of rows of `M`. -/
def CodesOf (M : Finset (Fin m → Bool)) (Mc : List ℕ) : Prop :=
  Mc.Nodup ∧ ∀ x ∈ Mc, x < 2 ^ m ∧ (dec x : Fin m → Bool) ∈ M

instance (M : Finset (Fin m → Bool)) (Mc : List ℕ) : Decidable (CodesOf M Mc) := by
  unfold CodesOf
  infer_instance

/-- **The bound by the search**, on histories. -/
theorem Gen.lt_of_check {S : Fin m → Bool} {A : Finset (Fin m → Bool)} {U : Set (Fin m)} {r b : ℕ} {M : Finset (Fin m → Bool)} {Mc : List ℕ}
    (h : Gen .multiple S A U r) (hMA : M ⊆ A) (hMc : CodesOf M Mc) (hcheck : check m Mc b = false) : b < r :=
  LabelSearch.lt_of_check hMc.1 hcheck h fun x hx => ⟨dec x, hMA (hMc.2 x hx).2, code_dec (hMc.2 x hx).1⟩

/-- **The bound by the search**, on networks, in any crossover model. -/
theorem Network.lt_recombCount_of_check {V E : Type*} [Finite V] {c : Crossover} (N : Network (Fin m) V E) (hc : N.Obeys c) {M : Finset (Fin m → Bool)} (hd : N.Derives M) {Mc : List ℕ}
    (hMc : CodesOf M Mc) {b : ℕ} (hcheck : check m Mc b = false) : b < N.recombCount := by
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  refine hg.toMultiple.lt_of_check (M := M) (fun r hr => ?_) hMc hcheck
  obtain ⟨v, -, rfl⟩ := hd.surjOn hr
  exact hlab v

end Bound

end Gusfield2007
