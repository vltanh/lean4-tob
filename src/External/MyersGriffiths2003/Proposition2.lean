module

public import External.MyersGriffiths2003.SampleHistory
public import Gusfield2007.ExplicitNetworks

/-!
# Proposition 2 of Myers and Griffiths, and the true minimum of the example

Myers and Griffiths 2003, p. 380 and Appendix B: "For a sample `S` of size `n`, the minimum number `R_S` of recombinations in the sample history until the MRCA is equal to `R_{S'}`, where the new sample `S'` is formed from `S` by either of the following two events: (1) coalescence of two sample members of the same type and (2) removal of a noninformative site."

Event (1) is the identity here, since `R` is a function of the set of rows. For (2), the proof is the source's. "Removing this mutation from the appropriate branch" gives `R_{S'} ≤ R_S`, which is `R_restrictRows_le_breakCount`. For the other, "there exists a unique sequence `l` in `S`, which is the only representative of one of the two types present at `m`. ... Form `H` through first mutating the ancestral line to `l`, at `m`": a new node with the site, below a node with the rest of `l` (`addPendantSite`). The sites are segregating, `NoConstantColumn`, as in the source.
-/

@[expose] public section

namespace MyersGriffiths2003

open Gusfield2007 Gusfield2007.Network

open scoped Classical

universe u v w

section AddSite

variable {ι : Type u} {V : Type v} {E : Type w} {s : ι}

/-- The label of a new node with the state `!b` at `s`, on the sites other than `s`. -/
noncomputable def extendLabel (s : ι) (b : Bool) (x : ({s}ᶜ : Set ι) → Bool) : ι → Bool := fun i => if h : i = s then b else x ⟨i, h⟩

/-- A network with one more site: all its nodes have the state `b` there, and a new node below `v₀` has the state `!b`, on the new arc that has the site. "The ancestor to `l` is now of the same type as `l'`". -/
noncomputable def addPendantSite (N : Network ({s}ᶜ : Set ι) V E) (v₀ : V) (b : Bool) : Network ι (Option V) (Option E) where
  src g := match g with
    | none => some v₀
    | some e => some (N.src e)
  tgt g := match g with
    | none => none
    | some e => some (N.tgt e)
  root := some N.root
  site i := if h : i = s then none else some (N.site ⟨i, h⟩)
  label w := match w with
    | none => extendLabel s (!b) (N.label v₀)
    | some v => extendLabel s b (N.label v)
  simple := by
    rintro (- | e) (- | f) h₁ h₂
    · rfl
    · simp at h₂
    · simp at h₂
    · exact congrArg some (N.simple e f (Option.some.inj h₁) (Option.some.inj h₂))
  acyclic := by
    have key : ∀ x w, Relation.TransGen (fun a b : Option V => ∃ g : Option E, (match g with
        | none => some v₀
        | some e => some (N.src e)) = a ∧ (match g with
        | none => none
        | some e => some (N.tgt e)) = b) (some x) w → w = none ∨ ∃ y, w = some y ∧ Relation.TransGen (fun a b => ∃ e, N.src e = a ∧ N.tgt e = b) x y := by
      intro x w h
      induction h with
      | single hstep =>
        obtain ⟨g, h₁, h₂⟩ := hstep
        cases g with
        | none => exact Or.inl h₂.symm
        | some e => exact Or.inr ⟨_, h₂.symm, Relation.TransGen.single ⟨e, Option.some.inj h₁, rfl⟩⟩
      | tail _ hstep ih =>
        obtain ⟨g, h₁, h₂⟩ := hstep
        rcases ih with rfl | ⟨y, rfl, hy⟩
        · cases g <;> simp at h₁
        · cases g with
          | none => exact Or.inl h₂.symm
          | some e => exact Or.inr ⟨_, h₂.symm, hy.tail ⟨e, Option.some.inj h₁, rfl⟩⟩
    rintro (- | x) h
    · obtain ⟨c, ⟨g, h₁, -⟩, -⟩ := Relation.TransGen.head'_iff.1 h
      cases g <;> simp at h₁
    · rcases key x _ h with h₁ | ⟨y, h₁, h₂⟩
      · simp at h₁
      · obtain rfl := Option.some.inj h₁
        exact N.acyclic _ h₂
  root_iff := by
    rintro (- | v)
    · exact ⟨fun h => absurd rfl (h none), fun h => by simp at h⟩
    · constructor
      · intro h
        exact congrArg some ((N.root_iff v).1 fun e he => h (some e) (congrArg some he))
      · intro h
        obtain rfl := Option.some.inj h
        rintro (- | e) he
        · simp at he
        · exact (N.root_iff N.root).2 rfl e (Option.some.inj he)
  inDegree_le_two := by
    rintro (- | e) (- | f) (- | g) h₁ h₂
    · exact Or.inl rfl
    · simp at h₂
    · simp at h₁
    · simp at h₁
    · simp at h₁
    · simp at h₁
    · simp at h₂
    · rcases N.inDegree_le_two e f g (Option.some.inj h₁) (Option.some.inj h₂) with h | h | h
      · exact Or.inl (congrArg some h)
      · exact Or.inr (Or.inl (congrArg some h))
      · exact Or.inr (Or.inr (congrArg some h))
  site_not_recomb := by
    intro i f hf
    by_cases hi : i = s
    · simp only [hi, ↓reduceDIte] at hf ⊢
      cases f with
      | none => rfl
      | some e => simp at hf
    · simp only [hi, ↓reduceDIte] at hf ⊢
      cases f with
      | none => simp at hf
      | some e => exact congrArg some (N.site_not_recomb ⟨i, hi⟩ e (Option.some.inj hf))
  label_tree := by
    rintro (- | e) he i
    · by_cases hi : i = s
      · simp [hi, extendLabel]
      · simp [hi, extendLabel]
    · have he' : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => Option.some.inj (he (some f) (congrArg some hf))
      by_cases hi : i = s
      · simp [hi, extendLabel]
      · have := N.label_tree e he' ⟨i, hi⟩
        simp only [hi, ↓reduceDIte, extendLabel, Option.some.injEq]
        exact this
  label_recomb := by
    rintro (- | e) (- | f) hef h i
    · exact absurd rfl hef
    · simp at h
    · simp at h
    · have hef' : e ≠ f := fun h' => hef (congrArg some h')
      by_cases hi : i = s
      · simp [hi, extendLabel]
      · have := N.label_recomb e f hef' (Option.some.inj h) ⟨i, hi⟩
        simpa only [hi, ↓reduceDIte, extendLabel] using this

variable {N : Network ({s}ᶜ : Set ι) V E} {v₀ : V} {b : Bool}

theorem isRecomb_addPendantSite {x : Option V} (h : (addPendantSite N v₀ b).IsRecomb x) : ∃ x', x = some x' ∧ N.IsRecomb x' := by
  obtain ⟨e, f, hef, he, hf⟩ := h
  rcases e with - | e <;> rcases f with - | f
  · exact absurd rfl hef
  · exact absurd (he.trans hf.symm) (by simp [addPendantSite])
  · exact absurd (he.trans hf.symm) (by simp [addPendantSite])
  · exact ⟨N.tgt e, he.symm, e, f, fun h' => hef (congrArg some h'), rfl, Option.some.inj (show some (N.tgt f) = some (N.tgt e) from hf.trans he.symm)⟩

theorem recombCount_addPendantSite_le [Finite V] : (addPendantSite N v₀ b).recombCount ≤ N.recombCount := by
  refine Nat.card_le_card_of_surjective (fun x : {x // N.IsRecomb x} => (⟨some x.1, ?_⟩ : {x // (addPendantSite N v₀ b).IsRecomb x})) ?_
  · obtain ⟨e, f, hef, he, hf⟩ := x.2
    exact ⟨some e, some f, fun h => hef (Option.some.inj h), congrArg some he, congrArg some hf⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x', rfl, hx'⟩ := isRecomb_addPendantSite hx
    exact ⟨⟨x', hx'⟩, rfl⟩

/-- A single crossover stays one. The new site has the same state in both parents, so the lower set of sites is any that extends the old one. -/
theorem obeys_addPendantSite_single [LinearOrder ι] (h : N.Obeys .single) : (addPendantSite N v₀ b).Obeys .single := by
  rw [obeys_iff] at h ⊢
  intro x hx
  obtain ⟨x', rfl, hx'⟩ := isRecomb_addPendantSite hx
  obtain ⟨e, f, hef, he, hf, L, hL⟩ := h x' hx'
  refine ⟨some e, some f, fun h' => hef (Option.some.inj h'), congrArg some he, congrArg some hf, ⟨{i | ∃ j ∈ L, i ≤ j.val}, fun a c hca ⟨j, hj, haj⟩ => ⟨j, hj, hca.trans haj⟩⟩, fun i => ?_⟩
  by_cases hi : i = s
  · subst hi
    change extendLabel i b (N.label x') i = if _ then extendLabel i b (N.label (N.src e)) i else extendLabel i b (N.label (N.src f)) i
    simp [extendLabel]
  · have hmem : (i ∈ ({i | ∃ j ∈ L, i ≤ j.val} : Set ι)) ↔ (⟨i, hi⟩ : ({s}ᶜ : Set ι)) ∈ L := by
      constructor
      · rintro ⟨j, hj, hij⟩
        exact L.lower (show (⟨i, hi⟩ : ({s}ᶜ : Set ι)) ≤ j from hij) hj
      · exact fun h' => ⟨_, h', le_rfl⟩
    change extendLabel s b (N.label x') i = if i ∈ ({i | ∃ j ∈ L, i ≤ j.val} : Set ι) then extendLabel s b (N.label (N.src e)) i else extendLabel s b (N.label (N.src f)) i
    have := hL ⟨i, hi⟩
    simp only [extendLabel, hi, ↓reduceDIte, hmem]
    exact this

/-- **The network with the noninformative site put back** (`ext:mg_prop2_back`). The row `l` is the only one in the other state at `s`. -/
theorem exists_network_of_row [LinearOrder ι] [Finite ι] [Finite V] [Finite E] {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M) {l : ι → Bool} (hl : l ∈ M)
    (hlb : l s = !b) (hall : ∀ r ∈ M, r ≠ l → r s = b) (hd : ∀ r ∈ restrictRows ({s}ᶜ : Set ι) M, ∃ v, N.label v = r) :
    ∃ (a c : ℕ) (N' : Network ι (Fin a) (Fin c)), (N.Obeys .single → N'.Obeys .single) ∧ N'.Derives M ∧ N'.ancestral = extendLabel s b N.ancestral ∧ N'.recombCount ≤ N.recombCount := by
  obtain ⟨v₁, hv₁⟩ := hd _ (mem_restrictRows.2 ⟨l, hl, rfl⟩)
  have hdisp : ∀ r ∈ M, ∃ w, (addPendantSite N v₁ b).label w = r := by
    intro r hr
    by_cases hrl : r = l
    · subst hrl
      refine ⟨none, funext fun i => ?_⟩
      change extendLabel s (!b) (N.label v₁) i = r i
      unfold extendLabel
      by_cases hi : i = s
      · simp only [hi, ↓reduceDIte, hlb]
      · simp only [hi, ↓reduceDIte, hv₁]
        rfl
    · obtain ⟨v, hv⟩ := hd _ (mem_restrictRows.2 ⟨r, hr, rfl⟩)
      refine ⟨some v, funext fun i => ?_⟩
      change extendLabel s b (N.label v) i = r i
      unfold extendLabel
      by_cases hi : i = s
      · simp only [hi, ↓reduceDIte, hall r hr hrl]
      · simp only [hi, ↓reduceDIte, hv]
        rfl
  obtain ⟨a, c, N', h₁, h₂, h₃, h₄⟩ := exists_derives_of_displays (addPendantSite N v₁ b) hM hC hdisp
  exact ⟨a, c, N', fun h => h₁ _ (obeys_addPendantSite_single h), h₂, h₃, h₄.trans recombCount_addPendantSite_le⟩

end AddSite

section Main

variable {S : ℕ} {M : Finset (Fin S → Bool)} {s : Fin S} {A : Option (Fin S → Bool)}

/-- A noninformative site, in a column that isn't constant, has one row in the other state. -/
theorem exists_row_of_isNoninformative (hC : NoConstantColumn M) (hs : IsNoninformative A M s) :
    ∃ l ∈ M, ∃ b, l s = !b ∧ (∀ r ∈ M, r ≠ l → r s = b) ∧ ∀ S₀, A = some S₀ → b = S₀ s := by
  have hboth : ∀ x : Bool, ∃ r ∈ M, r s = x := by
    obtain ⟨r, hr, r', hr', hne⟩ := hC s
    intro x
    by_cases h : r s = x
    · exact ⟨r, hr, h⟩
    · refine ⟨r', hr', ?_⟩
      revert h hne
      cases r s <;> cases r' s <;> cases x <;> simp
  have key : ∀ x : Bool, stateCount M s x ≤ 1 → ∃ l ∈ M, l s = x ∧ ∀ r ∈ M, r ≠ l → r s = !x := by
    intro x hx
    obtain ⟨l, hl, hlx⟩ := hboth x
    refine ⟨l, hl, hlx, fun r hr hne => ?_⟩
    by_contra hc
    have hrx : r s = x := by
      revert hc
      cases r s <;> cases x <;> simp
    exact hne (Finset.card_le_one.1 hx r (Finset.mem_filter.2 ⟨hr, hrx⟩) l (Finset.mem_filter.2 ⟨hl, hlx⟩))
  cases A with
  | none =>
    rcases hs with h | h
    · obtain ⟨l, hl, h₁, h₂⟩ := key true h
      exact ⟨l, hl, false, h₁, h₂, fun _ h' => by cases h'⟩
    · obtain ⟨l, hl, h₁, h₂⟩ := key false h
      exact ⟨l, hl, true, h₁, h₂, fun _ h' => by cases h'⟩
  | some S₀ =>
    obtain ⟨l, hl, h₁, h₂⟩ := key (!S₀ s) hs
    refine ⟨l, hl, S₀ s, h₁, fun r hr hne => ?_, fun _ h' => by cases h'; rfl⟩
    have := h₂ r hr hne
    simpa using this

/-- **Proposition 2, unknown types** (`ext:mg_prop2`). Removing a noninformative site doesn't change the minimum: `R¹(M') = R¹(M)`, and the same for multiple crossovers, which the source doesn't treat. -/
theorem proposition2 (hM : M.Nonempty) (hC : NoConstantColumn M) (hs : IsNoninformative none M s) :
    R .single (restrictRows ({s}ᶜ : Set (Fin S)) M) = R .single M ∧ R .multiple (restrictRows ({s}ᶜ : Set (Fin S)) M) = R .multiple M := by
  obtain ⟨l, hl, b, hlb, hall, -⟩ := exists_row_of_isNoninformative hC hs
  have hM' : (restrictRows ({s}ᶜ : Set (Fin S)) M).Nonempty := ⟨_, mem_restrictRows.2 ⟨hM.choose, hM.choose_spec, rfl⟩⟩
  constructor
  · refine le_antisymm ?_ ?_
    · obtain ⟨a, c, N, hc, hd, h⟩ := Nat.sInf_mem (recombSet_nonempty .single hM)
      refine (R_restrictRows_le_breakCount N hc hM hC hd.displays _).trans ((breakCount_le_recombCount N _).trans ?_)
      exact le_of_eq h
    · obtain ⟨a, c, N, hc, hd, h⟩ := Nat.sInf_mem (recombSet_nonempty .single hM')
      obtain ⟨a', c', N', h₁, h₂, -, h₄⟩ := exists_network_of_row (N := N) (b := b) hM hC hl hlb hall hd.displays
      have hle : R .single M ≤ N'.recombCount := Nat.sInf_le ⟨a', c', N', h₁ hc, h₂, rfl⟩
      exact hle.trans (h₄.trans (le_of_eq h))
  · refine le_antisymm ?_ ?_
    · obtain ⟨a, c, N, -, hd, h⟩ := Nat.sInf_mem (recombSet_nonempty .multiple hM)
      refine (R_multiple_restrictRows_le_breakCount N hM hC hd.displays _).trans ((breakCount_le_recombCount N _).trans ?_)
      exact le_of_eq h
    · obtain ⟨a, c, N, -, hd, h⟩ := Nat.sInf_mem (recombSet_nonempty .multiple hM')
      obtain ⟨a', c', N', -, h₂, -, h₄⟩ := exists_network_of_row (N := N) (b := b) hM hC hl hlb hall hd.displays
      have hle : R .multiple M ≤ N'.recombCount := Nat.sInf_le ⟨a', c', N', trivial, h₂, rfl⟩
      exact hle.trans (h₄.trans (le_of_eq h))

/-- **Proposition 2, known types** (`ext:mg_prop2_rooted`), with the ancestral sequence restricted to the other sites. -/
theorem proposition2_rooted (hM : M.Nonempty) (hC : NoConstantColumn M) (S₀ : Fin S → Bool) (hs : IsNoninformative (some S₀) M s) :
    RS .single (({s}ᶜ : Set (Fin S)).domRestrict S₀) (restrictRows ({s}ᶜ : Set (Fin S)) M) = RS .single S₀ M ∧
      RS .multiple (({s}ᶜ : Set (Fin S)).domRestrict S₀) (restrictRows ({s}ᶜ : Set (Fin S)) M) = RS .multiple S₀ M := by
  obtain ⟨l, hl, b, hlb, hall, hbS⟩ := exists_row_of_isNoninformative hC hs
  have hb : b = S₀ s := hbS S₀ rfl
  have hM' : (restrictRows ({s}ᶜ : Set (Fin S)) M).Nonempty := ⟨_, mem_restrictRows.2 ⟨hM.choose, hM.choose_spec, rfl⟩⟩
  have hext : ∀ {X : ({s}ᶜ : Set (Fin S)) → Bool}, X = ({s}ᶜ : Set (Fin S)).domRestrict S₀ → extendLabel s b X = S₀ := by
    rintro _ rfl
    funext i
    unfold extendLabel
    by_cases hi : i = s
    · simp only [hi, ↓reduceDIte, hb]
    · simp only [hi, ↓reduceDIte]
      rfl
  constructor
  · refine le_antisymm ?_ ?_
    · obtain ⟨a, c, N, hc, hd, hr, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .single S₀ hM)
      have := RS_restrictRows_le_breakCount N hc hM hC hd.displays ({s}ᶜ : Set (Fin S))
      rw [hr] at this
      exact this.trans ((breakCount_le_recombCount N _).trans (le_of_eq h))
    · obtain ⟨a, c, N, hc, hd, hr, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .single (({s}ᶜ : Set (Fin S)).domRestrict S₀) hM')
      obtain ⟨a', c', N', h₁, h₂, h₃, h₄⟩ := exists_network_of_row (N := N) (b := b) hM hC hl hlb hall hd.displays
      have hle : RS .single S₀ M ≤ N'.recombCount := Nat.sInf_le ⟨a', c', N', h₁ hc, h₂, h₃.trans (hext hr), rfl⟩
      exact hle.trans (h₄.trans (le_of_eq h))
  · refine le_antisymm ?_ ?_
    · obtain ⟨a, c, N, -, hd, hr, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .multiple S₀ hM)
      have := RS_multiple_restrictRows_le_breakCount N hM hC hd.displays ({s}ᶜ : Set (Fin S))
      rw [hr] at this
      exact this.trans ((breakCount_le_recombCount N _).trans (le_of_eq h))
    · obtain ⟨a, c, N, -, hd, hr, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .multiple (({s}ᶜ : Set (Fin S)).domRestrict S₀) hM')
      obtain ⟨a', c', N', -, h₂, h₃, h₄⟩ := exists_network_of_row (N := N) (b := b) hM hC hl hlb hall hd.displays
      have hle : RS .multiple S₀ M ≤ N'.recombCount := Nat.sInf_le ⟨a', c', N', trivial, h₂, h₃.trans (hext hr), rfl⟩
      exact hle.trans (h₄.trans (le_of_eq h))

end Main

/-! ### The true minimum of the example -/

/-- A history of the source's example, with ancestor `0000` and four recombinations. The nodes in order: `0000`, `1000`, `1100`, `1110`, `1001`, then the recombinants `0110`, `0101`, `1101`, `1111`, and leaves for the rows at internal nodes. It isn't the source's, which doesn't give one. -/
def exampleHistory : NetSpec 4 15 18 :=
  ⟨[0, 1, 2, 1, 0, 3, 5, 4, 1, 6, 3, 6, 0, 2, 3, 4, 5, 6],
   [1, 2, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 12, 13, 14],
   [0, 1, 2, 3],
   [0, 1, 3, 7, 9, 6, 10, 11, 15, 0, 3, 7, 9, 6, 10]⟩

theorem exampleHistory_valid : exampleHistory.Valid := by decide +kernel

theorem exampleHistory_derives : exampleHistory.DerivesCheck exampleSample := by decide +kernel

theorem exampleHistory_single : exampleHistory.SingleCheck := by decide +kernel

theorem exampleHistory_recombs : exampleHistory.recombs = 4 := by decide +kernel

theorem exampleHistory_root : exampleHistory.label 0 = fun _ => false := by decide +kernel

/-- **"In fact, we can easily construct a history with exactly four recombinations in this case, so four is the true minimum"** (`ext:mg_example_true_min`, p. 382), with the types known, as the example has them: `R_s = R¹_S(M) = 4`. -/
theorem exampleSample_RS : RS .single (fun _ => false) exampleSample = 4 := by
  refine le_antisymm ?_ ?_
  · have := NetSpec.RS_le exampleHistory_valid exampleHistory_derives (c := .single) (NetSpec.obeys_single_toNetwork _ exampleHistory_single) exampleHistory_root
    rwa [exampleHistory_recombs] at this
  · have h := RsKnown_le_RS (S := 4) (M := exampleSample) (by decide +kernel) (fun _ => false) (by norm_num)
    rwa [exampleSample_Rs.2.1] at h

end MyersGriffiths2003
