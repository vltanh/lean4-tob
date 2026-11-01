module

public import External.MyersGriffiths2003.Implementation

/-!
# The bound `R_s` of Myers and Griffiths: Algorithm 3 and Proposition 2

Myers and Griffiths 2003, pp. 380-381 and Appendix B. Coalesce sequences of the same type, remove noninformative sites, and when neither can be done remove a sequence, counting that removal as a recombination. "The bound produced is the minimum number of removals over the different choices of recombinants."

* `historyBound`: **Algorithm 3**, a computable function. A set of rows is coalesced by being a set. `A` is what's known of the ancestor: `none` for unknown types, `some S₀` for known ones, which is what the definition of noninformative depends on.
* `historyBound_le_breakCount`: it's a lower bound on the recombination nodes that break the sites;
* `Rs`, `RsKnown`, with `Rs_le_R`, `RsKnown_le_RS`: `R_s` is Algorithm 1 on these local bounds;
* `Rh_le_Rs`, `Rh_addRow_le_RsKnown`: `R_h ≤ R_s`, by `typeCount_le_historyBound`;
* `historyBound_substate_le`: the bound is "increasing in the number of segregating sites";
* in `External.MyersGriffiths2003.Proposition2`: **Proposition 2** (`proposition2`, `proposition2_rooted`), and the example of the source: `R_s = 4`, and "four is the true minimum" (`exampleSample_RS`).

**What's different in the proof of Algorithm 3.** The source argues by induction on the number of sequences, on an optimal history. It uses Proposition 2 to pass to the reduced data, and "the first event back in time must be a recombination to an ancestor of the sample, since no other event type is possible", and it follows the ancestors of the other sequences in that history. Here the history is a set `P` of nodes of a network, closed under parents. Its last node `v` is the first event back in time, and `P` without `v` is the history of what remains. Only the inequality `R_{S'} ≤ R_S` of Proposition 2 is used, in the form that a network with the rows on some sites has them on fewer. The cases are the source's: `v` isn't needed for a row (a coalescence or nothing), it has a site, which is then noninformative, or it's a recombination, which is the removal.
-/

@[expose] public section

namespace MyersGriffiths2003

open Gusfield2007 Gusfield2007.Network

universe v w

section Compute

variable {S : ℕ}

/-- The number of rows in the state `b` at the site `s`. -/
def stateCount (M : Finset (Fin S → Bool)) (s : Fin S) (b : Bool) : ℕ := (M.filter fun r => r s = b).card

/-- **Noninformative sites** (Proposition 2). "If the ancestral type at a segregating site is known, it is defined as noninformative if and only if exactly one member of the sample is of the mutant type. If the ancestral type is unknown, the site is noninformative if and only if all but one of the sample members are of the same type at that site." Here it's "at most one": a site with none, which stops being segregating when sequences are removed, can go too. -/
def IsNoninformative : Option (Fin S → Bool) → Finset (Fin S → Bool) → Fin S → Prop
  | none, M, s => stateCount M s true ≤ 1 ∨ stateCount M s false ≤ 1
  | some S₀, M, s => stateCount M s (!S₀ s) ≤ 1

instance : ∀ (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) (s : Fin S), Decidable (IsNoninformative A M s)
  | none, _, _ => inferInstanceAs (Decidable (_ ∨ _))
  | some _, _, _ => inferInstanceAs (Decidable (_ ≤ _))

/-- A row without the site `s`: its state there is set to `false`, for all rows alike. -/
def removeSite (s : Fin S) (r : Fin S → Bool) : Fin S → Bool := fun a => if a = s then false else r a

/-- The first noninformative site among `T`. -/
def firstNoninformative (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : Option (Fin S) :=
  (List.finRange S).find? fun s => decide (s ∈ T) && decide (IsNoninformative A M s)

/-- Algorithm 3, with a bound on the number of steps: the number `historyBound` uses is enough (`historyBoundFuel_eq`). -/
def historyBoundFuel (A : Option (Fin S → Bool)) : ℕ → Finset (Fin S → Bool) → Finset (Fin S) → ℕ
  | 0, _, _ => 0
  | n + 1, M, T =>
    if h : M.card ≤ 1 then 0 else
      match firstNoninformative A M T with
      | some s => historyBoundFuel A n (M.image (removeSite s)) (T.erase s)
      | none => M.inf' (Finset.card_pos.1 (by omega)) fun a => 1 + historyBoundFuel A n (M.erase a) T

/-- **Algorithm 3** (`ext:mg_algorithm3`) on the rows `M`, at the sites `T`. "If two sequences in `S` are of the same haplotype, coalesce them. If a site `s` is noninformative, remove the data corresponding to `s` from `S`. Repeat while it is still possible to perform such an event and more than one sequence remains in `S`. If only one sequence remains at this point, record the number of removal events ... Otherwise more than one sequence remains; choose one of the remaining sequences and remove it", over all the choices. -/
def historyBound (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : ℕ :=
  historyBoundFuel A (M.card + T.card) M T

/-- The sites between `i` and `j`, with both. -/
def regionSites (S i j : ℕ) : Finset (Fin S) := Finset.univ.filter fun a => i ≤ a.val ∧ a.val ≤ j

/-- The rows at the sites `T`. -/
def rowsAt (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : Finset (Fin S → Bool) := M.image fun r a => decide (a ∈ T) && r a

/-- The local bounds of `R_s`: "to obtain a local bound for the region between sites `i` and `j`, we can construct a data set corresponding to the types of all the sample members at just the sites within that region". -/
def historyBounds (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) : ℕ → ℕ → ℕ := fun i j =>
  historyBound A (rowsAt M (regionSites S i j)) (regionSites S i j)

/-- **`R_s`, for unknown types** (`ext:mg_rs`): "using Algorithm 1 on the local bounds results in the statistic `R_s`". -/
def Rs (M : Finset (Fin S → Bool)) : ℕ := algorithm1 (historyBounds none M) S 0 (S - 1)

/-- **`R_s`, for known types** (`ext:mg_rs_known`). -/
def RsKnown (S₀ : Fin S → Bool) (M : Finset (Fin S → Bool)) : ℕ := algorithm1 (historyBounds (some S₀) M) S 0 (S - 1)

/-- **The example of the source** (`ext:mg_example_rs`). With known types, all `0`, the local bounds of Algorithm 3 are the matrix `B^S` of (6), and `R_s = 4`, and the source's `2 = R_m < R_h < R_s = 4`. With unknown types, which the source doesn't compute here, the bound is `3`. -/
theorem exampleSample_Rs :
    (∀ i j : Fin 4, i < j → historyBounds (some fun _ => false) exampleSample i j = exampleBS i j) ∧
      RsKnown (fun _ => false) exampleSample = 4 ∧ Rs exampleSample = 3 := by
  decide +kernel

end Compute

open scoped Classical

/-! ### The steps of Algorithm 3 -/

section Steps

variable {S : ℕ} {A : Option (Fin S → Bool)} {M : Finset (Fin S → Bool)} {T : Finset (Fin S)} {s : Fin S}

theorem firstNoninformative_some (h : firstNoninformative A M T = some s) : s ∈ T ∧ IsNoninformative A M s := by
  have := (List.find?_eq_some_iff_append.1 h).1
  simpa using this

theorem firstNoninformative_none (h : firstNoninformative A M T = none) : ∀ s ∈ T, ¬ IsNoninformative A M s := by
  intro s hs hn
  refine List.find?_eq_none.1 h s (List.mem_finRange s) ?_
  simp [hs, hn]

theorem card_image_removeSite_le (M : Finset (Fin S → Bool)) (s : Fin S) : (M.image (removeSite s)).card ≤ M.card := Finset.card_image_le

/-- Enough steps give the same value: one more step changes nothing. -/
theorem historyBoundFuel_succ (A : Option (Fin S → Bool)) (n : ℕ) :
    ∀ (M : Finset (Fin S → Bool)) (T : Finset (Fin S)), M.card + T.card ≤ n → historyBoundFuel A (n + 1) M T = historyBoundFuel A n M T := by
  induction n with
  | zero =>
    intro M T h
    have hM : M.card ≤ 1 := by omega
    simp only [historyBoundFuel, hM, ↓reduceDIte]
  | succ n ih =>
    intro M T h
    rw [historyBoundFuel, historyBoundFuel]
    by_cases hM : M.card ≤ 1
    · simp only [hM, ↓reduceDIte]
    · simp only [hM, ↓reduceDIte]
      cases hf : firstNoninformative A M T with
      | some s =>
        simp only
        refine ih _ _ ?_
        have h₁ := card_image_removeSite_le M s
        have h₂ := Finset.card_erase_of_mem (firstNoninformative_some hf).1
        have h₃ := Finset.card_pos.2 ⟨s, (firstNoninformative_some hf).1⟩
        omega
      | none =>
        simp only
        refine Finset.inf'_congr _ rfl fun a ha => ?_
        rw [ih _ _ (by
          have := Finset.card_erase_of_mem ha
          omega)]

theorem historyBoundFuel_eq {n : ℕ} (h : M.card + T.card ≤ n) : historyBoundFuel A n M T = historyBound A M T := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [historyBoundFuel_succ A n M T hn, ih]

theorem historyBound_of_card_le (h : M.card ≤ 1) : historyBound A M T = 0 := by
  rw [← historyBoundFuel_eq (n := M.card + T.card + 1) (by omega), historyBoundFuel]
  simp only [h, ↓reduceDIte]

/-- A noninformative site is removed. -/
theorem historyBound_of_some (h : ¬ M.card ≤ 1) (hf : firstNoninformative A M T = some s) :
    historyBound A M T = historyBound A (M.image (removeSite s)) (T.erase s) := by
  rw [← historyBoundFuel_eq (n := M.card + T.card + 1) (by omega), historyBoundFuel]
  simp only [h, ↓reduceDIte, hf]
  refine historyBoundFuel_eq ?_
  have h₁ := card_image_removeSite_le M s
  have h₂ := Finset.card_erase_le (s := T) (a := s)
  omega

/-- A sequence is removed, the best choice of it. -/
theorem historyBound_of_none (h : ¬ M.card ≤ 1) (hf : firstNoninformative A M T = none) :
    historyBound A M T = M.inf' (Finset.card_pos.1 (by omega)) fun a => 1 + historyBound A (M.erase a) T := by
  rw [← historyBoundFuel_eq (n := M.card + T.card + 1) (by omega), historyBoundFuel]
  simp only [h, ↓reduceDIte, hf]
  refine Finset.inf'_congr _ rfl fun a ha => ?_
  rw [historyBoundFuel_eq]
  have := Finset.card_erase_le (s := M) (a := a)
  omega

/-- The rows are at the sites `T`: their other states are `false`. -/
def Masked (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : Prop := ∀ r ∈ M, ∀ a, a ∉ T → r a = false

theorem Masked.eq {M : Finset (Fin S → Bool)} {T : Finset (Fin S)} (h : Masked M T) {r r' : Fin S → Bool} (hr : r ∈ M) (hr' : r' ∈ M) (he : ∀ a ∈ T, r a = r' a) : r = r' := by
  funext a
  by_cases ha : a ∈ T
  · exact he a ha
  · rw [h r hr a ha, h r' hr' a ha]

theorem Masked.erase (h : Masked M T) (a : Fin S → Bool) : Masked (M.erase a) T := fun r hr => h r (Finset.mem_of_mem_erase hr)

theorem Masked.removeSite (h : Masked M T) (s : Fin S) : Masked (M.image (removeSite s)) (T.erase s) := by
  intro r hr a ha
  obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hr
  unfold MyersGriffiths2003.removeSite
  by_cases has : a = s
  · rw [ite_eq_left has]
  · rw [ite_eq_right has]
    exact h r₀ hr₀ a fun haT => ha (Finset.mem_erase.2 ⟨has, haT⟩)

theorem masked_rowsAt (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : Masked (rowsAt M T) T := by
  intro r hr a ha
  obtain ⟨r₀, -, rfl⟩ := Finset.mem_image.1 hr
  simp [ha]

/-- A site where all rows but one have the state `b` is noninformative, when `b` is the ancestor's if that's known. -/
theorem isNoninformative_of_all_but_one {r : Fin S → Bool} {b : Bool} (hA : ∀ S₀, A = some S₀ → S₀ s = b) (h : ∀ r' ∈ M, r' ≠ r → r' s = b) : IsNoninformative A M s := by
  have hcount : stateCount M s (!b) ≤ 1 := by
    refine Finset.card_le_one.2 fun x hx y hy => ?_
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.1 hx
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_filter.1 hy
    by_cases hxr : x = r
    · by_cases hyr : y = r
      · rw [hxr, hyr]
      · have := h y hy₁ hyr
        rw [this] at hy₂
        cases b <;> simp at hy₂
    · have := h x hx₁ hxr
      rw [this] at hx₂
      cases b <;> simp at hx₂
  cases A with
  | none =>
    cases b
    · exact Or.inl hcount
    · exact Or.inr hcount
  | some S₀ =>
    have : S₀ s = b := hA S₀ rfl
    change stateCount M s (!S₀ s) ≤ 1
    rw [this]
    exact hcount

end Steps

/-! ### Algorithm 3 is a lower bound -/

section Bound

variable {S : ℕ} {V : Type v} {E : Type w} [Fintype V]

omit [Fintype V] in
/-- A node reaching a node of a set closed under parents is in the set. -/
theorem mem_of_reach_of_closed (N : Network (Fin S) V E) {P : Finset V} (hcl : ∀ e, N.tgt e ∈ P → N.src e ∈ P) {c u : V} (h : N.Reach c u) (hu : u ∈ P) : c ∈ P := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hu
  | head hstep _ ih =>
    obtain ⟨e, rfl, rfl⟩ := hstep
    exact hcl e ih

/-- **The proof of Algorithm 3** (`ext:mg_algorithm3_bound`). A set `P` of nodes closed under parents, with the root, is a history. If it has the rows on the sites `T`, Algorithm 3 is at most the number of its recombination nodes that break `T`. See the module's docstring for the proof, which is the source's induction, on the size of `P` as well, and for the only difference. -/
theorem historyBound_le_card (N : Network (Fin S) V E) {A : Option (Fin S → Bool)} (hA : ∀ S₀, A = some S₀ → N.label N.root = S₀) (n : ℕ) :
    ∀ (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) (P : Finset V), M.card + T.card + P.card ≤ n → N.root ∈ P → (∀ e, N.tgt e ∈ P → N.src e ∈ P) → Masked M T →
      (∀ r ∈ M, ∃ v ∈ P, ∀ a ∈ T, N.label v a = r a) → historyBound A M T ≤ (P.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))).card := by
  have hrootno : ∀ e, N.tgt e ≠ N.root := (N.root_iff N.root).2 rfl
  induction n with
  | zero =>
    intro M T P hsize hr
    exact absurd (Finset.card_pos.2 ⟨_, hr⟩) (by omega)
  | succ n ih =>
    intro M T P hsize hr hcl hmask hdisp
    by_cases h₁ : M.card ≤ 1
    · rw [historyBound_of_card_le h₁]
      exact Nat.zero_le _
    cases hf : firstNoninformative A M T with
    | some s =>
      -- A noninformative site is removed: fewer sites, and fewer nodes break them.
      obtain ⟨hsT, -⟩ := firstNoninformative_some hf
      rw [historyBound_of_some h₁ hf]
      have hle := card_image_removeSite_le M s
      have herase := Finset.card_erase_of_mem hsT
      have hpos := Finset.card_pos.2 ⟨s, hsT⟩
      refine (ih _ _ P (by omega) hr hcl (hmask.removeSite s) ?_).trans (Finset.card_le_card fun x hx => ?_)
      · intro r hr'
        obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.1 hr'
        obtain ⟨v, hv, hl⟩ := hdisp r₀ hr₀
        refine ⟨v, hv, fun a ha => ?_⟩
        obtain ⟨has, haT⟩ := Finset.mem_erase.1 ha
        rw [hl a haT]
        unfold removeSite
        rw [ite_eq_right has]
      · obtain ⟨hx₁, hx₂, hx₃⟩ := Finset.mem_filter.1 hx
        refine Finset.mem_filter.2 ⟨hx₁, hx₂, breaksAt_mono hx₃ ?_⟩
        exact Finset.coe_subset.2 (Finset.erase_subset _ _)
    | none =>
      -- The last node of the history.
      have hnonroot : (P.erase N.root).Nonempty := by
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (not_le.1 h₁)
        obtain ⟨u, hu, hul⟩ := hdisp x hx
        obtain ⟨u', hu', hul'⟩ := hdisp y hy
        have hne : u ≠ u' := by
          rintro rfl
          exact hxy (hmask.eq hx hy fun a ha => (hul a ha).symm.trans (hul' a ha))
        by_cases hu₀ : u = N.root
        · exact ⟨u', Finset.mem_erase.2 ⟨fun h => hne (hu₀.trans h.symm), hu'⟩⟩
        · exact ⟨u, Finset.mem_erase.2 ⟨hu₀, hu⟩⟩
      obtain ⟨v, hv, hmin⟩ := N.wellFounded_transGen_swap.has_min (↑(P.erase N.root) : Set V) (by
        rw [Finset.coe_nonempty]
        exact hnonroot)
      have hvP : v ∈ P := Finset.mem_of_mem_erase hv
      have hvr : v ≠ N.root := Finset.ne_of_mem_erase hv
      have hno : ∀ e, N.src e = v → N.tgt e ∉ P := fun e he htP =>
        hmin _ (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hrootno e, htP⟩)) (Relation.TransGen.single ⟨e, he, rfl⟩)
      set P' := P.erase v with hP'
      have hP'card : P'.card + 1 = P.card := Finset.card_erase_add_one hvP
      have hrP' : N.root ∈ P' := Finset.mem_erase.2 ⟨hvr.symm, hr⟩
      have hclP' : ∀ e, N.tgt e ∈ P' → N.src e ∈ P' := fun e he => by
        have hteP := Finset.mem_of_mem_erase he
        exact Finset.mem_erase.2 ⟨fun h => hno e h hteP, hcl e hteP⟩
      have hclP'' : ∀ {e}, N.tgt e = v → N.src e ∈ P' := fun {e} hev =>
        Finset.mem_erase.2 ⟨fun h => hno e h (hev ▸ hvP), hcl e (hev ▸ hvP)⟩
      have hcountle : (P'.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))).card ≤ (P.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
      by_cases hall : ∀ r ∈ M, ∃ u ∈ P', ∀ a ∈ T, N.label u a = r a
      · -- The node isn't needed for a row: a coalescence, or nothing.
        exact (ih M T P' (by omega) hrP' hclP' hmask hall).trans hcountle
      · push Not at hall
        obtain ⟨r, hrM, hrno⟩ := hall
        -- The node is the only one with the row `r`.
        have hvlab : ∀ a ∈ T, N.label v a = r a := by
          obtain ⟨u, hu, hul⟩ := hdisp r hrM
          by_cases huv : u = v
          · rw [← huv]
            exact hul
          · obtain ⟨a, ha, hne⟩ := hrno u (Finset.mem_erase.2 ⟨huv, hu⟩)
            exact absurd (hul a ha) hne
        have hother : ∀ r' ∈ M, r' ≠ r → ∃ u ∈ P', ∀ a ∈ T, N.label u a = r' a := by
          intro r' hr' hne
          obtain ⟨u, hu, hul⟩ := hdisp r' hr'
          refine ⟨u, Finset.mem_erase.2 ⟨?_, hu⟩, hul⟩
          rintro rfl
          exact hne (hmask.eq hr' hrM fun a ha => (hul a ha).symm.trans (hvlab a ha))
        by_cases hrec : N.IsRecomb v
        · by_cases hb : N.BreaksAt v (T : Set (Fin S))
          · -- The first event back in time is a recombination: the removal of `r`.
            have hIH := ih (M.erase r) T P' (by
              have := Finset.card_erase_of_mem hrM
              omega) hrP' hclP' (hmask.erase r) (fun r' hr' => hother r' (Finset.mem_of_mem_erase hr') (Finset.ne_of_mem_erase hr'))
            have hcard : (P.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))).card = (P'.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))).card + 1 := by
              have hins : (P.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))) = insert v (P'.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))) := by
                ext x
                simp only [Finset.mem_filter, Finset.mem_insert, hP', Finset.mem_erase]
                constructor
                · rintro ⟨h₂, h₃⟩
                  by_cases hxv : x = v
                  · exact Or.inl hxv
                  · exact Or.inr ⟨⟨hxv, h₂⟩, h₃⟩
                · rintro (rfl | ⟨⟨-, h₂⟩, h₃⟩)
                  · exact ⟨hvP, hrec, hb⟩
                  · exact ⟨h₂, h₃⟩
              rw [hins, Finset.card_insert_of_notMem]
              intro hmem
              exact Finset.notMem_erase v P (Finset.mem_of_mem_filter _ hmem)
            rw [historyBound_of_none h₁ hf, hcard]
            refine (Finset.inf'_le _ hrM).trans ?_
            omega
          · -- A recombination that is a copy of a parent on `T`: that parent has the row.
            exfalso
            unfold BreaksAt at hb
            push Not at hb
            obtain ⟨e, hev, hl⟩ := hb
            have hsrc : N.src e ∈ P' := hclP'' hev
            obtain ⟨a, ha, hne⟩ := hrno _ hsrc
            refine hne ?_
            rw [← hvlab a ha]
            exact (congrFun hl ⟨a, Finset.mem_coe.2 ha⟩).symm
        · -- A node with one arc in.
          exfalso
          obtain ⟨e, hev⟩ : ∃ e, N.tgt e = v := by
            by_contra hc
            push Not at hc
            exact hvr ((N.root_iff v).1 hc)
          have huniq : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => by
            by_contra hne
            exact hrec ⟨f, e, hne, hf.trans hev, hev⟩
          by_cases hsite : ∃ s ∈ T, N.site s = e
          · -- A site on the arc: the other rows don't have it, so that it's noninformative.
            obtain ⟨s, hsT, hse⟩ := hsite
            refine firstNoninformative_none hf s hsT (isNoninformative_of_all_but_one (r := r) (b := N.label N.root s) ?_ ?_)
            · intro S₀ hS₀
              rw [hA S₀ hS₀]
            · intro r' hr' hne
              obtain ⟨u, hu, hul⟩ := hother r' hr' hne
              rw [← hul s hsT]
              by_contra hoff
              have hreach := N.reach_of_label_ne hoff
              rw [hse, hev] at hreach
              have huv : u ≠ v := Finset.ne_of_mem_erase hu
              rcases Relation.ReflTransGen.cases_head hreach with h₂ | ⟨c, ⟨g, hg, rfl⟩, h₃⟩
              · exact huv h₂.symm
              · exact hno g hg (mem_of_reach_of_closed N hcl h₃ (Finset.mem_of_mem_erase hu))
          · -- No site on the arc: the parent has the row.
            push Not at hsite
            have hsrc : N.src e ∈ P' := hclP'' hev
            obtain ⟨a, ha, hne⟩ := hrno _ hsrc
            refine hne ?_
            have hl := N.label_tree e huniq a
            rw [ite_eq_right (hsite a ha), hev] at hl
            rw [← hl]
            exact hvlab a ha

/-- **Algorithm 3 is a lower bound** (`ext:mg_algorithm3_le`): at most the number of recombination nodes of a network that break the sites `T`, for a network with the rows among the labels of its nodes. "The algorithm returns the minimum number of removal events over possible histories of `S`", which is "at most `D_S`, the true minimum". For known types, the root is the ancestor. -/
theorem historyBound_le_breakCount [Finite E] (N : Network (Fin S) V E) {A : Option (Fin S → Bool)} (hA : ∀ S₀, A = some S₀ → N.label N.root = S₀) {M : Finset (Fin S → Bool)}
    (hd : ∀ r ∈ M, ∃ v, N.label v = r) (T : Finset (Fin S)) : historyBound A (rowsAt M T) T ≤ breakCount N (T : Set (Fin S)) := by
  have hcount : breakCount N (T : Set (Fin S)) = (Finset.univ.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S))).card := by
    unfold breakCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcount]
  refine historyBound_le_card N hA _ _ T Finset.univ le_rfl (Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) (masked_rowsAt M T) ?_
  intro r hr
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨v, rfl⟩ := hd ρ hρ
  refine ⟨v, Finset.mem_univ _, fun a ha => ?_⟩
  simp [ha]

end Bound

/-! ### `R_s` -/

section Rs

variable {S : ℕ}

theorem coe_regionSites (i j : ℕ) : (regionSites S i j : Set (Fin S)) = region S i j := by
  ext a
  simp [regionSites, region]

/-- **The local bounds of Algorithm 3 are local bounds** (`ext:mg_local_history`). -/
theorem isLocalBounds_historyBounds (M : Finset (Fin S → Bool)) : IsLocalBounds M (historyBounds none M) := by
  intro a b N _ hd i j _ _
  have := historyBound_le_breakCount (A := none) N (fun S₀ h => by cases h) hd (regionSites S i j)
  rwa [coe_regionSites] at this

/-- **`R_s` is a lower bound on `R¹`** (`ext:mg_rs_le`). -/
theorem Rs_le_R {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hS : 0 < S) : Rs M ≤ R .single M :=
  algorithm1_le_R hM (isLocalBounds_historyBounds M) (Nat.zero_le _) (by omega)

/-- **`R_s` with known types is a lower bound on `R¹_S`** (`ext:mg_rs_known_le`). -/
theorem RsKnown_le_RS {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (S₀ : Fin S → Bool) (hS : 0 < S) : RsKnown S₀ M ≤ RS .single S₀ M := by
  obtain ⟨a, b, N, hc, hd, hroot, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .single S₀ hM)
  have hB : ∀ i j, i < j → j < S → historyBounds (some S₀) M i j ≤ breakCount N (region S i j) := by
    intro i j _ _
    have := historyBound_le_breakCount (A := some S₀) N (fun S₁ h₁ => by
      rw [Option.some.inj h₁] at hroot
      exact hroot) hd.displays (regionSites S i j)
    rwa [coe_regionSites] at this
  have := algorithm1_le_recombCount N hc hB (s := 0) (t := S - 1) (Nat.zero_le _) (by omega)
  rw [h] at this
  exact this

/-- The rows that the types are counted on: those of the sample, and the ancestor if it's known. -/
noncomputable def withAncestor (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) : Finset (Fin S → Bool) :=
  match A with
  | none => M
  | some S₀ => addRow M S₀

theorem image_addRow (f : (Fin S → Bool) → Fin S → Bool) (M : Finset (Fin S → Bool)) (S₀ : Fin S → Bool) :
    (addRow M S₀).image f = insert (f S₀) (M.image f) := by
  ext y
  simp only [Finset.mem_image, mem_addRow, Finset.mem_insert]
  constructor
  · rintro ⟨r, rfl | hr, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨r, hr, rfl⟩
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨S₀, Or.inl rfl, rfl⟩
    · exact ⟨r, Or.inr hr, rfl⟩

theorem card_addRow_le (M : Finset (Fin S → Bool)) (S₀ : Fin S → Bool) : (addRow M S₀).card ≤ M.card + 1 := by
  have h := image_addRow id M S₀
  simp only [Finset.image_id] at h
  rw [h]
  exact Finset.card_insert_le _ _

/-- A site with at most one row in a state is compatible with every site. -/
theorem not_incompatible_of_stateCount_le {X : Finset (Fin S → Bool)} {s t : Fin S} {b : Bool} (h : (X.filter fun r => r s = b).card ≤ 1) : ¬ Incompatible X s t := by
  intro hinc
  obtain ⟨r, hr, h₁, h₂⟩ := hinc b true
  obtain ⟨r', hr', h₃, h₄⟩ := hinc b false
  have := Finset.card_le_one.1 h r (Finset.mem_filter.2 ⟨hr, h₁⟩) r' (Finset.mem_filter.2 ⟨hr', h₃⟩)
  rw [this] at h₂
  rw [h₂] at h₄
  exact Bool.noConfusion h₄

/-- A noninformative site is compatible with every other site, in the rows with the ancestor. So Lemma 4 applies to it. -/
theorem not_incompatible_of_isNoninformative {A : Option (Fin S → Bool)} {M : Finset (Fin S → Bool)} {s t : Fin S} (h : IsNoninformative A M s) :
    ¬ Incompatible (withAncestor A M) s t := by
  cases A with
  | none =>
    rcases h with h | h
    · exact not_incompatible_of_stateCount_le h
    · exact not_incompatible_of_stateCount_le h
  | some S₀ =>
    refine not_incompatible_of_stateCount_le (b := !S₀ s) ?_
    have hsub : ((addRow M S₀).filter fun r => r s = !S₀ s) ⊆ M.filter fun r => r s = !S₀ s := by
      intro r hr
      obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.1 hr
      rcases mem_addRow.1 hr₁ with rfl | hr₁
      · cases hb : r s <;> simp [hb] at hr₂
      · exact Finset.mem_filter.2 ⟨hr₁, hr₂⟩
    exact (Finset.card_le_card hsub).trans h

/-- Masking away a site that isn't counted doesn't change the types. -/
theorem typeCount_withAncestor_removeSite (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) {s : Fin S} {T : Finset (Fin S)} (hs : s ∉ T) :
    typeCount (withAncestor A (M.image (removeSite s))) T = typeCount (withAncestor A M) T := by
  have hmask : ∀ r : Fin S → Bool, (fun a => decide (a ∈ T) && removeSite s r a) = fun a => decide (a ∈ T) && r a := by
    intro r
    funext a
    by_cases ha : a ∈ T
    · have has : a ≠ s := fun h => hs (h ▸ ha)
      simp [removeSite, has]
    · simp [ha]
  have himage : (M.image (removeSite s)).image (fun r a => decide (a ∈ T) && r a) = M.image fun r a => decide (a ∈ T) && r a := by
    rw [Finset.image_image]
    exact Finset.image_congr fun r _ => hmask r
  cases A with
  | none =>
    unfold typeCount withAncestor
    rw [himage]
  | some S₀ =>
    unfold typeCount withAncestor
    rw [image_addRow, image_addRow, himage]

/-- Removing a row removes at most one type. -/
theorem typeCount_withAncestor_le_erase (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) (a : Fin S → Bool) (T : Finset (Fin S)) :
    typeCount (withAncestor A M) T ≤ typeCount (withAncestor A (M.erase a)) T + 1 := by
  have hsub : withAncestor A M ⊆ insert a (withAncestor A (M.erase a)) := by
    intro r hr
    by_cases hra : r = a
    · rw [hra]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem ?_
      cases A with
      | none => exact Finset.mem_erase.2 ⟨hra, hr⟩
      | some S₀ =>
        rcases mem_addRow.1 hr with rfl | hr'
        · exact mem_addRow.2 (Or.inl rfl)
        · exact mem_addRow.2 (Or.inr (Finset.mem_erase.2 ⟨hra, hr'⟩))
  unfold typeCount
  refine (Finset.card_le_card (Finset.image_subset_image hsub)).trans ?_
  rw [Finset.image_insert]
  exact Finset.card_insert_le _ _

/-- **`H - S' - 1` is at most Algorithm 3** (`ext:mg_haplotype_le_history`), on any subset of the sites. "The bound obtained through this method is easily seen to always equal or increase the haplotype bound for the corresponding region; it models the history more carefully": removing a noninformative site takes away one site and at most one type, by Lemma 4, removing a sequence takes away at most one type, and it's counted. -/
theorem typeCount_le_historyBound (A : Option (Fin S → Bool)) (n : ℕ) :
    ∀ (M : Finset (Fin S → Bool)) (U : Finset (Fin S)), M.card + U.card ≤ n → ∀ T ⊆ U, typeCount (withAncestor A M) T ≤ historyBound A M U + T.card + 1 := by
  induction n with
  | zero =>
    intro M U hsize T hT
    have hM : M.card ≤ 1 := by omega
    have hU : U = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [hU, Finset.subset_empty] at hT
    subst hT
    have : typeCount (withAncestor A M) ∅ ≤ 1 := by
      unfold typeCount
      refine Finset.card_le_one.2 fun x hx y hy => ?_
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 hy
      funext a
      simp
    omega
  | succ n ih =>
    intro M U hsize T hT
    by_cases h₁ : M.card ≤ 1
    · rw [historyBound_of_card_le h₁]
      by_cases hTe : T = ∅
      · subst hTe
        have : typeCount (withAncestor A M) ∅ ≤ 1 := by
          unfold typeCount
          refine Finset.card_le_one.2 fun x hx y hy => ?_
          obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 hy
          funext a
          simp
        omega
      · have hpos := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hTe)
        have hle : typeCount (withAncestor A M) T ≤ (withAncestor A M).card := Finset.card_image_le
        have hcard : (withAncestor A M).card ≤ M.card + 1 := by
          cases A with
          | none =>
            change M.card ≤ _
            omega
          | some S₀ => exact card_addRow_le M S₀
        omega
    cases hf : firstNoninformative A M U with
    | some s =>
      obtain ⟨hsU, hsn⟩ := firstNoninformative_some hf
      rw [historyBound_of_some h₁ hf]
      have hle := card_image_removeSite_le M s
      have herase := Finset.card_erase_of_mem hsU
      have hpos := Finset.card_pos.2 ⟨s, hsU⟩
      by_cases hsT : s ∈ T
      · have hsub : T.erase s ⊆ U.erase s := Finset.erase_subset_erase _ hT
        have hIH := ih (M.image (removeSite s)) (U.erase s) (by omega) (T.erase s) hsub
        rw [typeCount_withAncestor_removeSite A M (Finset.notMem_erase s T)] at hIH
        have hL := typeCount_le_erase_add_one (withAncestor A M) T s fun t _ _ => not_incompatible_of_isNoninformative hsn
        have hcardT := Finset.card_erase_of_mem hsT
        have hposT := Finset.card_pos.2 ⟨s, hsT⟩
        omega
      · have hsub : T ⊆ U.erase s := fun a ha => Finset.mem_erase.2 ⟨fun h => hsT (h ▸ ha), hT ha⟩
        have hIH := ih (M.image (removeSite s)) (U.erase s) (by omega) T hsub
        rwa [typeCount_withAncestor_removeSite A M hsT] at hIH
    | none =>
      rw [historyBound_of_none h₁ hf]
      obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' (Finset.card_pos.1 (by omega) : M.Nonempty) fun a => 1 + historyBound A (M.erase a) U
      rw [hmin]
      have hIH := ih (M.erase a) U (by
        have := Finset.card_erase_of_mem ha
        omega) T hT
      have hL := typeCount_withAncestor_le_erase A M a T
      omega

/-- The types at sites within `U` of the rows at `U` are the types of the rows. -/
theorem typeCount_rowsAt (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) {T U : Finset (Fin S)} (hT : T ⊆ U) :
    typeCount (withAncestor A (rowsAt M U)) T = typeCount (withAncestor A M) T := by
  have himage : (rowsAt M U).image (fun r a => decide (a ∈ T) && r a) = M.image fun r a => decide (a ∈ T) && r a := by
    unfold rowsAt
    rw [Finset.image_image]
    refine Finset.image_congr fun r _ => ?_
    funext a
    by_cases ha : a ∈ T
    · simp [ha, hT ha]
    · simp [ha]
  cases A with
  | none =>
    unfold typeCount withAncestor
    rw [himage]
  | some S₀ =>
    unfold typeCount withAncestor
    rw [image_addRow, image_addRow, himage]

/-- The haplotype bounds of the rows with the ancestor are at most the local bounds of Algorithm 3. -/
theorem haplotypeBounds_le_historyBounds (A : Option (Fin S → Bool)) (M : Finset (Fin S → Bool)) (i j : ℕ) :
    haplotypeBounds (withAncestor A M) i j ≤ historyBounds A M i j := by
  refine Finset.sup_le fun T hT => ?_
  have hsub : T ⊆ regionSites S i j := fun c hc => by
    have := (Finset.mem_filter.1 hT).2.2.2 c hc
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
  have h := typeCount_le_historyBound A _ (rowsAt M (regionSites S i j)) (regionSites S i j) le_rfl T hsub
  rw [typeCount_rowsAt A M hsub] at h
  unfold haplotypeAt historyBounds
  omega

/-- **`R_h ≤ R_s`** (`ext:mg_rh_le_rs`): "for any given data set `R_s ≥ R_h ≥ R_m`". -/
theorem Rh_le_Rs (M : Finset (Fin S → Bool)) (hS : 0 < S) : Rh M ≤ Rs M :=
  algorithm1_mono (fun i j _ _ => haplotypeBounds_le_historyBounds none M i j) (Nat.zero_le _) (by omega)

/-- **`R_h ≤ R_s` with known types** (`ext:mg_rh_le_rs_known`): `R_h` is computed on the rows with the all-zero type added. -/
theorem Rh_addRow_le_RsKnown (S₀ : Fin S → Bool) (M : Finset (Fin S → Bool)) (hS : 0 < S) : Rh (addRow M S₀) ≤ RsKnown S₀ M :=
  algorithm1_mono (fun i j _ _ => haplotypeBounds_le_historyBounds (some S₀) M i j) (Nat.zero_le _) (by omega)

end Rs

/-! ### More sites give a larger bound -/

section Mono

variable {S : ℕ} {A : Option (Fin S → Bool)}

/-- The rows `M'` at the sites `T'` are got from the rows `M` at the sites `T` by removing rows and sites. -/
structure IsSubstate (M' : Finset (Fin S → Bool)) (T' : Finset (Fin S)) (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : Prop where
  sites : T' ⊆ T
  masked' : Masked M' T'
  rows : ∀ y ∈ M', ∃ z ∈ M, ∀ a ∈ T', y a = z a

theorem IsSubstate.card_le {M' M : Finset (Fin S → Bool)} {T' T : Finset (Fin S)} (h : IsSubstate M' T' M T) : M'.card ≤ M.card := by
  choose! g hg₁ hg₂ using h.rows
  refine Finset.card_le_card_of_injOn g hg₁ fun y hy y' hy' he => ?_
  refine h.masked'.eq hy hy' fun a ha => ?_
  rw [hg₂ y hy a ha, hg₂ y' hy' a ha, he]

theorem IsSubstate.stateCount_le {M' M : Finset (Fin S → Bool)} {T' T : Finset (Fin S)} (h : IsSubstate M' T' M T) {s : Fin S} (hs : s ∈ T') (b : Bool) : stateCount M' s b ≤ stateCount M s b := by
  choose! g hg₁ hg₂ using h.rows
  refine Finset.card_le_card_of_injOn g (fun y hy => ?_) fun y hy y' hy' he => ?_
  · obtain ⟨hy₁, hy₂⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hg₁ y hy₁, ?_⟩)
    rw [← hg₂ y hy₁ s hs]
    exact hy₂
  · refine h.masked'.eq (Finset.mem_of_mem_filter _ (Finset.mem_coe.1 hy)) (Finset.mem_of_mem_filter _ (Finset.mem_coe.1 hy')) fun a ha => ?_
    rw [hg₂ y (Finset.mem_of_mem_filter _ (Finset.mem_coe.1 hy)) a ha, hg₂ y' (Finset.mem_of_mem_filter _ (Finset.mem_coe.1 hy')) a ha, he]

theorem IsSubstate.isNoninformative {M' M : Finset (Fin S → Bool)} {T' T : Finset (Fin S)} (h : IsSubstate M' T' M T) {s : Fin S} (hs : s ∈ T') (hn : IsNoninformative A M s) : IsNoninformative A M' s := by
  cases A with
  | none =>
    rcases hn with hn | hn
    · exact Or.inl ((h.stateCount_le hs true).trans hn)
    · exact Or.inr ((h.stateCount_le hs false).trans hn)
  | some S₀ => exact (h.stateCount_le hs _).trans hn

/-- Removing a site from both. -/
theorem IsSubstate.removeSite {M' M : Finset (Fin S → Bool)} {T' T : Finset (Fin S)} (h : IsSubstate M' T' M T) (s : Fin S) :
    IsSubstate (M'.image (removeSite s)) (T'.erase s) (M.image (removeSite s)) (T.erase s) := by
  refine ⟨Finset.erase_subset_erase _ h.sites, h.masked'.removeSite s, fun y hy => ?_⟩
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨z, hz, hyz⟩ := h.rows y₀ hy₀
  refine ⟨_, Finset.mem_image_of_mem _ hz, fun a ha => ?_⟩
  obtain ⟨has, haT⟩ := Finset.mem_erase.1 ha
  unfold MyersGriffiths2003.removeSite
  rw [ite_eq_right has, ite_eq_right has]
  exact hyz a haT

/-- **More rows and sites give a larger bound** (`ext:mg_history_mono`): "the bound obtained is obviously increasing in the number of segregating sites in the sample". It isn't obvious here, as the algorithm removes the first noninformative site, so the proof shows at the same time that any of them can go first, and that removing a sequence costs at most one. -/
theorem historyBound_steps (n : ℕ) :
    ∀ (M : Finset (Fin S → Bool)) (T : Finset (Fin S)), M.card + T.card ≤ n → Masked M T →
      (∀ s ∈ T, IsNoninformative A M s → historyBound A M T ≤ historyBound A (M.image (removeSite s)) (T.erase s)) ∧
      (∀ a ∈ M, historyBound A M T ≤ 1 + historyBound A (M.erase a) T) ∧
      ∀ (M' : Finset (Fin S → Bool)) (T' : Finset (Fin S)), IsSubstate M' T' M T → historyBound A M' T' ≤ historyBound A M T := by
  induction n with
  | zero =>
    intro M T hsize _
    have hM : M.card ≤ 1 := by omega
    refine ⟨fun _ _ _ => by rw [historyBound_of_card_le hM]; exact Nat.zero_le _, fun _ _ => by rw [historyBound_of_card_le hM]; exact Nat.zero_le _, fun M' T' h => ?_⟩
    rw [historyBound_of_card_le (h.card_le.trans hM)]
    exact Nat.zero_le _
  | succ n ih =>
    intro M T hsize hmask
    have hsmall : ∀ {s : Fin S}, s ∈ T → (M.image (MyersGriffiths2003.removeSite s)).card + (T.erase s).card ≤ n := by
      intro s hs
      have h₁ := card_image_removeSite_le M s
      have h₂ := Finset.card_erase_of_mem hs
      have h₃ := Finset.card_pos.2 ⟨s, hs⟩
      omega
    have hsmall' : ∀ {a : Fin S → Bool}, a ∈ M → (M.erase a).card + T.card ≤ n := by
      intro a ha
      have h₁ := Finset.card_erase_of_mem ha
      have h₂ := Finset.card_pos.2 ⟨a, ha⟩
      omega
    -- Any noninformative site can go first.
    have hany : ∀ s ∈ T, IsNoninformative A M s → historyBound A M T ≤ historyBound A (M.image (removeSite s)) (T.erase s) := by
      intro s hsT hsn
      by_cases h₁ : M.card ≤ 1
      · rw [historyBound_of_card_le h₁]
        exact Nat.zero_le _
      cases hf : firstNoninformative A M T with
      | none => exact absurd hsn (firstNoninformative_none hf s hsT)
      | some s₀ =>
        obtain ⟨hs₀T, hs₀n⟩ := firstNoninformative_some hf
        rw [historyBound_of_some h₁ hf]
        by_cases hss : s = s₀
        · rw [hss]
        · have hsT₀ : s ∈ T.erase s₀ := Finset.mem_erase.2 ⟨hss, hsT⟩
          have hmask₀ := hmask.removeSite s₀
          have hsub₀ : IsSubstate (M.image (removeSite s₀)) (T.erase s₀) M T :=
            ⟨Finset.erase_subset _ _, hmask₀, fun y hy => by
              obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
              refine ⟨z, hz, fun a ha => ?_⟩
              unfold MyersGriffiths2003.removeSite
              rw [ite_eq_right (Finset.ne_of_mem_erase ha)]⟩
          have hIH₀ := ih _ _ (hsmall hs₀T) hmask₀
          refine (hIH₀.1 s hsT₀ (hsub₀.isNoninformative hsT₀ hsn)).trans ?_
          have hIH := ih _ _ (hsmall hsT) (hmask.removeSite s)
          refine hIH.2.2 _ _ ⟨?_, hmask₀.removeSite s, fun y hy => ?_⟩
          · exact Finset.erase_subset_erase _ (Finset.erase_subset _ _)
          · obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hy
            obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy₀
            refine ⟨_, Finset.mem_image_of_mem _ hz, fun a ha => ?_⟩
            obtain ⟨has, haT⟩ := Finset.mem_erase.1 ha
            unfold MyersGriffiths2003.removeSite
            rw [ite_eq_right has, ite_eq_right has, ite_eq_right (Finset.ne_of_mem_erase haT)]
    -- Removing a sequence costs at most one.
    have hcost : ∀ a ∈ M, historyBound A M T ≤ 1 + historyBound A (M.erase a) T := by
      intro a ha
      by_cases h₁ : M.card ≤ 1
      · rw [historyBound_of_card_le h₁]
        exact Nat.zero_le _
      cases hf : firstNoninformative A M T with
      | none =>
        rw [historyBound_of_none h₁ hf]
        exact Finset.inf'_le (fun a => 1 + historyBound A (M.erase a) T) ha
      | some s₀ =>
        obtain ⟨hs₀T, -⟩ := firstNoninformative_some hf
        rw [historyBound_of_some h₁ hf]
        have hmask₀ := hmask.removeSite s₀
        have hIH₀ := ih _ _ (hsmall hs₀T) hmask₀
        have ha₀ : removeSite s₀ a ∈ M.image (removeSite s₀) := Finset.mem_image_of_mem _ ha
        refine (hIH₀.2.1 _ ha₀).trans (Nat.add_le_add_left ?_ 1)
        refine (ih _ _ (hsmall' ha) (hmask.erase a)).2.2 _ _ ⟨Finset.erase_subset _ _, hmask₀.erase _, fun y hy => ?_⟩
        obtain ⟨hne, hy₁⟩ := Finset.mem_erase.1 hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy₁
        refine ⟨z, Finset.mem_erase.2 ⟨fun h => hne (by rw [h]), hz⟩, fun b hb => ?_⟩
        unfold MyersGriffiths2003.removeSite
        rw [ite_eq_right (Finset.ne_of_mem_erase hb)]
    refine ⟨hany, hcost, fun M' T' hsub => ?_⟩
    -- The same state.
    by_cases heq : M' = M ∧ T' = T
    · rw [heq.1, heq.2]
    have hM'le := hsub.card_le
    have hT'le := Finset.card_le_card hsub.sites
    have hsmaller : M'.card + T'.card ≤ n := by
      by_contra hc
      have hT'eq : T' = T := Finset.eq_of_subset_of_card_le hsub.sites (by omega)
      have hM'eq : M' = M := by
        have hsubM : M' ⊆ M := by
          intro y hy
          obtain ⟨z, hz, hyz⟩ := hsub.rows y hy
          have : y = z := by
            funext a
            by_cases ha : a ∈ T'
            · exact hyz a ha
            · rw [hsub.masked' y hy a ha, hmask z hz a (hT'eq ▸ ha)]
          rw [this]
          exact hz
        exact Finset.eq_of_subset_of_card_le hsubM (by omega)
      exact heq ⟨hM'eq, hT'eq⟩
    have hIH' := ih M' T' hsmaller hsub.masked'
    by_cases h₁ : M.card ≤ 1
    · rw [historyBound_of_card_le (hM'le.trans h₁)]
      exact Nat.zero_le _
    cases hf : firstNoninformative A M T with
    | some s₀ =>
      obtain ⟨hs₀T, hs₀n⟩ := firstNoninformative_some hf
      rw [historyBound_of_some h₁ hf]
      have hIH₀ := ih _ _ (hsmall hs₀T) (hmask.removeSite s₀)
      by_cases hs₀ : s₀ ∈ T'
      · refine (hIH'.1 s₀ hs₀ (hsub.isNoninformative hs₀ hs₀n)).trans ?_
        exact hIH₀.2.2 _ _ (hsub.removeSite s₀)
      · refine hIH₀.2.2 _ _ ⟨fun a ha => Finset.mem_erase.2 ⟨fun h => hs₀ (h ▸ ha), hsub.sites ha⟩, hsub.masked', fun y hy => ?_⟩
        obtain ⟨z, hz, hyz⟩ := hsub.rows y hy
        refine ⟨_, Finset.mem_image_of_mem _ hz, fun a ha => ?_⟩
        unfold MyersGriffiths2003.removeSite
        rw [ite_eq_right (show a ≠ s₀ from fun h => hs₀ (h ▸ ha))]
        exact hyz a ha
    | none =>
      rw [historyBound_of_none h₁ hf]
      obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' (Finset.card_pos.1 (by omega) : M.Nonempty) fun a => 1 + historyBound A (M.erase a) T
      rw [hmin]
      have hIHa := ih _ _ (hsmall' ha) (hmask.erase a)
      -- The type of `a` at `T'`.
      set y₀ : Fin S → Bool := fun b => decide (b ∈ T') && a b with hy₀
      have hne : ∀ y ∈ M', y ≠ y₀ → ∃ z ∈ M.erase a, ∀ b ∈ T', y b = z b := by
        intro y hy hyne
        obtain ⟨z, hz, hyz⟩ := hsub.rows y hy
        refine ⟨z, Finset.mem_erase.2 ⟨?_, hz⟩, hyz⟩
        rintro rfl
        apply hyne
        funext b
        by_cases hb : b ∈ T'
        · simp [hy₀, hb, hyz b hb]
        · simp [hy₀, hb, hsub.masked' y hy b hb]
      by_cases hmem : y₀ ∈ M'
      · refine (hIH'.2.1 y₀ hmem).trans (Nat.add_le_add_left ?_ 1)
        exact hIHa.2.2 _ _ ⟨hsub.sites, hsub.masked'.erase _, fun y hy => hne y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)⟩
      · have := hIHa.2.2 M' T' ⟨hsub.sites, hsub.masked', fun y hy => hne y hy fun h => hmem (h ▸ hy)⟩
        omega

/-- **The bound is monotone** (`ext:mg_history_mono`). "Unlike for the haplotype bounds there is no point in taking further subsets of this set, since the bound obtained is obviously increasing in the number of segregating sites in the sample." -/
theorem historyBound_rowsAt_le (M : Finset (Fin S → Bool)) {T' T : Finset (Fin S)} (h : T' ⊆ T) :
    historyBound A (rowsAt M T') T' ≤ historyBound A (rowsAt M T) T := by
  refine (historyBound_steps _ _ _ le_rfl (masked_rowsAt M T)).2.2 _ _ ⟨h, masked_rowsAt M T', fun y hy => ?_⟩
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
  refine ⟨_, Finset.mem_image_of_mem _ hr, fun a ha => ?_⟩
  simp [ha, h ha]

end Mono

end MyersGriffiths2003
