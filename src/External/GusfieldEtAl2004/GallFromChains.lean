module

public import External.GusfieldEtAl2004.ReducedUnrooted

/-!
# A gall from two chains of rows (Gusfield, Eddhu, Langley 2004, Section 3.2)

Theorem 3.2 of the source: "There is a sequence `f` in `M(C)`, such that after removal of all copies of `f`, there is a perfect phylogeny for the resulting matrix; the labeled edges of that perfect phylogeny contain all sites in `C` organized into one or two paths; and the recombination of the two 'end' sequences [...] creates sequence `f`."
This module is the construction: two chains of rows, disjoint, whose ends recombine to `s`, make a network with one recombination node, whose nodes are the rows.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network

variable {κ : Type*}

section Chains

variable (S₀ : κ → Bool)

/-- The sites where a row has another state than `S₀`. -/
def fl (r : κ → Bool) : Set κ := {i | r i ≠ S₀ i}

/-- The end of a set of rows: another state than `S₀` where some row has one. On a chain this is the largest row, and on no rows it is `S₀`. -/
def topRow (X : Finset (κ → Bool)) : κ → Bool := fun i => if ∃ r ∈ X, r i ≠ S₀ i then !S₀ i else S₀ i

variable {S₀}

theorem fl_injective {a b : κ → Bool} (h : fl S₀ a = fl S₀ b) : a = b := by
  funext i
  have hi : a i ≠ S₀ i ↔ b i ≠ S₀ i := by
    have := Set.ext_iff.1 h i
    exact this
  revert hi
  cases a i <;> cases b i <;> cases S₀ i <;> simp

/-- A chain of rows, with no row equal to `S₀`. -/
structure IsChain (S₀ : κ → Bool) (X : Finset (κ → Bool)) : Prop where
  comparable : ∀ a ∈ X, ∀ b ∈ X, fl S₀ a ⊆ fl S₀ b ∨ fl S₀ b ⊆ fl S₀ a
  ne : ∀ a ∈ X, a ≠ S₀

variable [Finite κ] {X : Finset (κ → Bool)}

theorem IsChain.sub_of_ncard_le (hX : IsChain S₀ X) {a b : κ → Bool} (ha : a ∈ X) (hb : b ∈ X) (h : (fl S₀ a).ncard ≤ (fl S₀ b).ncard) : fl S₀ a ⊆ fl S₀ b := by
  rcases hX.comparable a ha b hb with h' | h'
  · exact h'
  · exact (Set.eq_of_subset_of_ncard_le h' h (Set.toFinite _)).symm.subset

theorem ncard_lt_of_sub {a b : κ → Bool} (h : fl S₀ a ⊆ fl S₀ b) (hne : a ≠ b) : (fl S₀ a).ncard < (fl S₀ b).ncard := by
  refine Set.ncard_lt_ncard ⟨h, fun h' => hne (fl_injective (Set.Subset.antisymm h h'))⟩ (Set.toFinite _)

/-- The row of a nonempty chain below which all the others are. -/
theorem IsChain.exists_max (hX : IsChain S₀ X) (hne : X.Nonempty) : ∃ y ∈ X, ∀ r ∈ X, fl S₀ r ⊆ fl S₀ y := by
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image X (fun r => (fl S₀ r).ncard) hne
  exact ⟨y, hy, fun r hr => hX.sub_of_ncard_le hr hy (hmax r hr)⟩

omit [Finite κ] in
/-- The end of a nonempty chain is its largest row. -/
theorem topRow_eq_of_max {y : κ → Bool} (hy : y ∈ X) (hmax : ∀ r ∈ X, fl S₀ r ⊆ fl S₀ y) : topRow S₀ X = y := by
  funext i
  by_cases h : y i ≠ S₀ i
  · have hb : ∀ {u v : Bool}, u ≠ v → (!v) = u := by decide
    rw [topRow, ite_eq_left ⟨y, hy, h⟩]
    exact hb h
  · push Not at h
    have hno : ¬ ∃ r ∈ X, r i ≠ S₀ i := by
      rintro ⟨r, hr, hri⟩
      exact hmax r hr hri h
    rw [topRow, ite_eq_right hno, h]

omit [Finite κ] in
/-- The states of the end of a set of rows. -/
theorem topRow_ne_iff {i : κ} : topRow S₀ X i ≠ S₀ i ↔ ∃ r ∈ X, r i ≠ S₀ i := by
  by_cases h : ∃ r ∈ X, r i ≠ S₀ i
  · simp only [topRow, h, ite_true, iff_true]
    cases S₀ i <;> simp
  · simp [topRow, h]

/-- The row just below a row of a chain, or `S₀`. -/
def predRow (S₀ : κ → Bool) (X : Finset (κ → Bool)) (r : κ → Bool) : κ → Bool :=
  if h : (X.filter fun y => (fl S₀ y).ncard < (fl S₀ r).ncard).Nonempty then (Finset.exists_max_image _ (fun y => (fl S₀ y).ncard) h).choose else S₀

theorem predRow_spec (hX : IsChain S₀ X) {r : κ → Bool} (hr : r ∈ X) :
    (predRow S₀ X r ∈ X ∨ predRow S₀ X r = S₀) ∧ (fl S₀ (predRow S₀ X r)).ncard < (fl S₀ r).ncard ∧ fl S₀ (predRow S₀ X r) ⊆ fl S₀ r ∧ ∀ y ∈ X, fl S₀ y ⊆ fl S₀ r → y ≠ r → fl S₀ y ⊆ fl S₀ (predRow S₀ X r) := by
  have hempty : fl S₀ S₀ = ∅ := by
    ext i
    simp [fl]
  have hrne : (fl S₀ r).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hX.ne r hr (fl_injective (h.trans hempty.symm))
  unfold predRow
  split_ifs with h
  · obtain ⟨hy, hmax⟩ := (Finset.exists_max_image _ (fun y => (fl S₀ y).ncard) h).choose_spec
    set y := (Finset.exists_max_image _ (fun y => (fl S₀ y).ncard) h).choose
    obtain ⟨hyX, hyr⟩ := Finset.mem_filter.1 hy
    refine ⟨Or.inl hyX, hyr, hX.sub_of_ncard_le hyX hr hyr.le, fun z hz hzr hne => ?_⟩
    exact hX.sub_of_ncard_le hz hyX (hmax z (Finset.mem_filter.2 ⟨hz, ncard_lt_of_sub hzr hne⟩))
  · rw [hempty]
    refine ⟨Or.inr rfl, ?_, Set.empty_subset _, fun z hz hzr hne => ?_⟩
    · rw [Set.ncard_empty]
      exact (Set.ncard_pos (Set.toFinite _)).2 hrne
    · exact absurd (Finset.mem_filter.2 ⟨hz, ncard_lt_of_sub hzr hne⟩) (fun hm => h ⟨z, hm⟩)

/-- The first row of a chain with another state at `i`. -/
theorem IsChain.exists_first (hX : IsChain S₀ X) {i : κ} (h : ∃ r ∈ X, r i ≠ S₀ i) : ∃ y ∈ X, y i ≠ S₀ i ∧ ∀ r ∈ X, r i ≠ S₀ i → fl S₀ y ⊆ fl S₀ r := by
  obtain ⟨r₀, hr₀, hi₀⟩ := h
  have hne : (X.filter fun r => r i ≠ S₀ i).Nonempty := ⟨r₀, Finset.mem_filter.2 ⟨hr₀, hi₀⟩⟩
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image _ (fun r => (fl S₀ r).ncard) hne
  obtain ⟨hyX, hyi⟩ := Finset.mem_filter.1 hy
  exact ⟨y, hyX, hyi, fun r hr hri => hX.sub_of_ncard_le hyX hr (hmin r (Finset.mem_filter.2 ⟨hr, hri⟩))⟩

end Chains

section Gall

variable [Finite κ] [LinearOrder κ] [DecidableEq (κ → Bool)] {S₀ s : κ → Bool} {A B : Finset (κ → Bool)}

/-- The hypotheses of the construction: two chains, disjoint in their sites, covering all the sites, and a recombinant of their ends that is on neither and isn't `S₀`. -/
structure IsArrangement (S₀ s : κ → Bool) (A B : Finset (κ → Bool)) (c : Crossover) : Prop where
  chainA : IsChain S₀ A
  chainB : IsChain S₀ B
  disj : ∀ a ∈ A, ∀ b ∈ B, ∀ i, a i ≠ S₀ i → b i = S₀ i
  nonempty : (A ∪ B).Nonempty
  cover : ∀ i, ∃ r ∈ A ∪ B, r i ≠ S₀ i
  sA : s ∉ A
  sB : s ∉ B
  sS : s ≠ S₀
  recomb : Recombinant c (topRow S₀ B) (topRow S₀ A) s

variable {c : Crossover}

/-- The nodes: the rows of the chains, `s`, and `S₀`. -/
abbrev GallNode (S₀ s : κ → Bool) (A B : Finset (κ → Bool)) : Type _ := {r // r ∈ insert S₀ (insert s (A ∪ B))}

omit [LinearOrder κ] [DecidableEq (κ → Bool)] in
theorem topRow_mem (hX : IsChain S₀ A) : topRow S₀ A ∈ A ∨ (topRow S₀ A = S₀ ∧ A = ∅) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · refine Or.inr ⟨?_, rfl⟩
    funext i
    simp [topRow]
  · obtain ⟨y, hy, hmax⟩ := hX.exists_max hne
    rw [topRow_eq_of_max hy hmax]
    exact Or.inl hy

/-- **A gall from two chains.** The source's Theorem 3.2 read backwards: an arrangement makes a network with the ancestral sequence `S₀`, in the model of the recombination, deriving the rows of the chains and `s`, with at most one recombination node. -/
theorem IsArrangement.exists_network (h : IsArrangement S₀ s A B c) :
    ∃ (a b : ℕ) (P : Network κ (Fin a) (Fin b)), P.Obeys c ∧ P.ancestral = S₀ ∧ P.Derives (insert s (A ∪ B)) ∧ P.recombCount ≤ 1 := by
  have hAB : ∀ r, r ∈ A → r ∉ B := by
    intro r hrA hrB
    have hne : r ≠ S₀ := h.chainA.ne r hrA
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ S₀ i := by
      by_contra hno
      push Not at hno
      exact hne (funext hno)
    exact hi (h.disj r hrA r hrB i hi)
  have hmemA : ∀ {r}, r ∈ A → r ∈ insert S₀ (insert s (A ∪ B)) := fun hr => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hr))
  have hmemB : ∀ {r}, r ∈ B → r ∈ insert S₀ (insert s (A ∪ B)) := fun hr => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hr))
  have hmemS : S₀ ∈ insert S₀ (insert s (A ∪ B)) := Finset.mem_insert_self _ _
  have hmems : s ∈ insert S₀ (insert s (A ∪ B)) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hchainMem : ∀ {X : Finset (κ → Bool)} {r}, (X = A ∨ X = B) → IsChain S₀ X → r ∈ X → predRow S₀ X r ∈ insert S₀ (insert s (A ∪ B)) := by
    rintro X r hX hch hr
    rcases (predRow_spec hch hr).1 with h' | h'
    · rcases hX with rfl | rfl
      · exact hmemA h'
      · exact hmemB h'
    · rw [h']
      exact hmemS
  have htopMem : ∀ {X : Finset (κ → Bool)}, (X = A ∨ X = B) → IsChain S₀ X → topRow S₀ X ∈ insert S₀ (insert s (A ∪ B)) := by
    rintro X hX hch
    rcases topRow_mem hch with h' | ⟨h', -⟩
    · rcases hX with rfl | rfl
      · exact hmemA h'
      · exact hmemB h'
    · rw [h']
      exact hmemS
  -- the first row of its chain with a site
  have hfirst : ∀ i, ∃ y, (y ∈ A ∧ y i ≠ S₀ i ∧ ∀ r ∈ A, r i ≠ S₀ i → fl S₀ y ⊆ fl S₀ r) ∨ (y ∈ B ∧ y i ≠ S₀ i ∧ ∀ r ∈ B, r i ≠ S₀ i → fl S₀ y ⊆ fl S₀ r) := by
    intro i
    obtain ⟨r, hr, hri⟩ := h.cover i
    rcases Finset.mem_union.1 hr with hrA | hrB
    · obtain ⟨y, h₁, h₂, h₃⟩ := h.chainA.exists_first ⟨r, hrA, hri⟩
      exact ⟨y, Or.inl ⟨h₁, h₂, h₃⟩⟩
    · obtain ⟨y, h₁, h₂, h₃⟩ := h.chainB.exists_first ⟨r, hrB, hri⟩
      exact ⟨y, Or.inr ⟨h₁, h₂, h₃⟩⟩
  choose siteRow hsiteRow using hfirst
  have hsiteMem : ∀ i, siteRow i ∈ insert S₀ (insert s (A ∪ B)) := fun i => by
    rcases hsiteRow i with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact hmemA h₁
    · exact hmemB h₁
  have hne_topA_topB : topRow S₀ A ≠ topRow S₀ B := by
    obtain ⟨r, hr⟩ := h.nonempty
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ S₀ i := by
      by_contra hno
      push Not at hno
      have hrS : r = S₀ := funext hno
      rcases Finset.mem_union.1 hr with h' | h'
      · exact h.chainA.ne r h' hrS
      · exact h.chainB.ne r h' hrS
    intro heq
    rcases Finset.mem_union.1 hr with h' | h'
    · have h₁ : topRow S₀ A i ≠ S₀ i := topRow_ne_iff.2 ⟨r, h', hi⟩
      rw [heq] at h₁
      obtain ⟨b, hb, hbi⟩ := topRow_ne_iff.1 h₁
      exact hbi (h.disj r h' b hb i hi)
    · have h₁ : topRow S₀ B i ≠ S₀ i := topRow_ne_iff.2 ⟨r, h', hi⟩
      rw [← heq] at h₁
      obtain ⟨a, ha, hai⟩ := topRow_ne_iff.1 h₁
      exact hi (h.disj a ha r h' i hai)
  -- the network
  let V := GallNode S₀ s A B
  have hparVal : ∀ r : V, r.1 ≠ S₀ → ∃ p : V, (r.1 ∈ A → p.1 = predRow S₀ A r.1) ∧ (r.1 ∈ B → p.1 = predRow S₀ B r.1) ∧ (r.1 = s → p.1 = topRow S₀ A) := by
    rintro ⟨r, hr⟩ hrS
    rcases Finset.mem_insert.1 hr with h' | hr
    · exact absurd h' hrS
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact ⟨⟨_, htopMem (Or.inl rfl) h.chainA⟩, fun h' => absurd h' h.sA, fun h' => absurd h' h.sB, fun _ => rfl⟩
    rcases Finset.mem_union.1 hr with h' | h'
    · exact ⟨⟨_, hchainMem (Or.inl rfl) h.chainA h'⟩, fun _ => rfl, fun h'' => absurd h'' (hAB r h'), fun h'' => absurd (h'' ▸ h') h.sA⟩
    · exact ⟨⟨_, hchainMem (Or.inr rfl) h.chainB h'⟩, fun h'' => absurd h' (hAB r h''), fun _ => rfl, fun h'' => absurd (h'' ▸ h') h.sB⟩
  choose! parV hparA hparB hparS using hparVal
  let P : PreNet κ V :=
    { root := ⟨S₀, hmemS⟩
      par := fun v => if v.1 = S₀ then none else some (parV v)
      par₂ := fun v => if v.1 = s then some ⟨_, htopMem (Or.inr rfl) h.chainB⟩ else none
      site := fun i => some ⟨siteRow i, hsiteMem i⟩
      label := fun v => v.1
      par_eq_none := by
        intro v
        by_cases hv : v.1 = S₀
        · simp only [hv, ite_true, true_iff]
          exact Subtype.ext hv
        · simp only [hv, ite_false, reduceCtorEq, false_iff]
          exact fun h' => hv (congrArg Subtype.val h')
      par₂_root := by
        simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
        exact fun h' => h.sS h'.symm
      par₂_ne := by
        intro v q hq hp
        by_cases hvs : v.1 = s
        · simp only [hvs, ite_true, Option.some.injEq] at hq
          have hvS : v.1 ≠ S₀ := fun h' => h.sS (hvs.symm.trans h')
          simp only [hvS, ite_false, Option.some.injEq] at hp
          have h₁ : q.1 = topRow S₀ B := by rw [← hq]
          have h₂ := hparS v hvS hvs
          rw [hp, h₁] at h₂
          exact hne_topA_topB h₂.symm
        · simp [hvs] at hq
      acyclic := by
        let ρ : V → ℕ := fun v => if v.1 = s then Nat.card κ + 1 else (fl S₀ v.1).ncard
        have hle : ∀ v : V, (fl S₀ v.1).ncard ≤ Nat.card κ := fun v => Set.ncard_le_card _
        refine acyclic_of_strict ρ ?_
        rintro a b (hab | hab)
        · by_cases hbS : b.1 = S₀
          · simp [hbS] at hab
          simp only [hbS, ite_false, Option.some.injEq] at hab
          subst hab
          by_cases hbs : b.1 = s
          · have h₁ := hparS b hbS hbs
            have hpne : (parV b).1 ≠ s := by
              rw [h₁]
              rcases topRow_mem h.chainA with h' | ⟨h', -⟩
              · exact fun h'' => h.sA (h'' ▸ h')
              · rw [h']
                exact h.sS.symm
            simp only [ρ, hbs, ite_true, hpne, ite_false]
            have := hle (parV b)
            omega
          · have hbmem : b.1 ∈ A ∨ b.1 ∈ B := by
              have := b.2
              rcases Finset.mem_insert.1 this with h' | this
              · exact absurd h' hbS
              rcases Finset.mem_insert.1 this with h' | this
              · exact absurd h' hbs
              exact Finset.mem_union.1 this
            have hlt : (fl S₀ (parV b).1).ncard < (fl S₀ b.1).ncard ∧ (parV b).1 ≠ s := by
              rcases hbmem with h' | h'
              · rw [hparA b hbS h']
                obtain ⟨h₁, h₂, -, -⟩ := predRow_spec h.chainA h'
                refine ⟨h₂, ?_⟩
                rcases h₁ with h₁ | h₁
                · exact fun h'' => h.sA (h'' ▸ h₁)
                · rw [h₁]
                  exact h.sS.symm
              · rw [hparB b hbS h']
                obtain ⟨h₁, h₂, -, -⟩ := predRow_spec h.chainB h'
                refine ⟨h₂, ?_⟩
                rcases h₁ with h₁ | h₁
                · exact fun h'' => h.sB (h'' ▸ h₁)
                · rw [h₁]
                  exact h.sS.symm
            simp only [ρ, hbs, ite_false, hlt.2]
            exact hlt.1
        · by_cases hbs : b.1 = s
          · simp only [hbs, ite_true, Option.some.injEq] at hab
            have ha : a.1 = topRow S₀ B := by rw [← hab]
            have hne : a.1 ≠ s := by
              rw [ha]
              rcases topRow_mem h.chainB with h' | ⟨h', -⟩
              · exact fun h'' => h.sB (h'' ▸ h')
              · rw [h']
                exact h.sS.symm
            simp only [ρ, hbs, ite_true, hne, ite_false]
            have := hle a
            omega
          · simp [hbs] at hab
      site_tree := by
        intro i v hv
        simp only [Option.some.injEq] at hv
        have hvr : v.1 = siteRow i := by rw [← hv]
        have hvmem : v.1 ∈ A ∨ v.1 ∈ B := by
          rw [hvr]
          rcases hsiteRow i with ⟨h₁, -⟩ | ⟨h₁, -⟩
          · exact Or.inl h₁
          · exact Or.inr h₁
        have hvs : v.1 ≠ s := by
          rcases hvmem with h' | h'
          · exact fun h'' => h.sA (h'' ▸ h')
          · exact fun h'' => h.sB (h'' ▸ h')
        refine ⟨by simp [hvs], fun h' => ?_⟩
        have hvS : v.1 = S₀ := congrArg Subtype.val h'
        rcases hvmem with h'' | h''
        · exact h.chainA.ne _ h'' hvS
        · exact h.chainB.ne _ h'' hvS
      label_tree := by
        intro v p hp hq i
        have hvS : v.1 ≠ S₀ := by
          intro h'
          simp [h'] at hp
        have hvs : v.1 ≠ s := by
          intro h'
          simp [h'] at hq
        simp only [hvS, ite_false, Option.some.injEq] at hp
        subst hp
        have hvmem : v.1 ∈ A ∨ v.1 ∈ B := by
          have := v.2
          rcases Finset.mem_insert.1 this with h' | this
          · exact absurd h' hvS
          rcases Finset.mem_insert.1 this with h' | this
          · exact absurd h' hvs
          exact Finset.mem_union.1 this
        have hb : ∀ {u v w : Bool}, u ≠ w → v = w → u = !v := by decide
        have hb' : ∀ {u v w : Bool}, u ≠ w → v ≠ w → u = v := by decide
        have hsiteEq : (some (⟨siteRow i, hsiteMem i⟩ : V) = some v) ↔ siteRow i = v.1 :=
          ⟨fun h' => congrArg Subtype.val (Option.some.inj h'), fun h' => congrArg some (Subtype.ext h')⟩
        suffices hgoal : v.1 i = if siteRow i = v.1 then !(parV v).1 i else (parV v).1 i by
          by_cases hy : siteRow i = v.1
          · rw [ite_eq_left (hsiteEq.2 hy)]
            rw [ite_eq_left hy] at hgoal
            exact hgoal
          · rw [ite_eq_right (fun h' => hy (hsiteEq.1 h'))]
            rw [ite_eq_right hy] at hgoal
            exact hgoal
        have hstep : ∀ {X : Finset (κ → Bool)}, IsChain S₀ X → v.1 ∈ X → (parV v).1 = predRow S₀ X v.1 → (v.1 i ≠ S₀ i → siteRow i ∈ X ∧ siteRow i i ≠ S₀ i ∧ ∀ r ∈ X, r i ≠ S₀ i → fl S₀ (siteRow i) ⊆ fl S₀ r) →
            v.1 i = if siteRow i = v.1 then !(parV v).1 i else (parV v).1 i := by
          intro X hch hvX hpar hsiteX
          obtain ⟨-, h₂, h₃, h₄⟩ := predRow_spec hch hvX
          rw [← hpar] at h₂ h₃ h₄
          by_cases hvi : v.1 i ≠ S₀ i
          · obtain ⟨hyX, hyi, hymin⟩ := hsiteX hvi
            by_cases hpi : (parV v).1 i ≠ S₀ i
            · -- the site is above
              have hne : siteRow i ≠ v.1 := by
                intro hyv
                have h₅ := hymin _ ?_ hpi
                · rw [hyv] at h₅
                  have := Set.ncard_le_ncard h₅ (Set.toFinite _)
                  omega
                · rcases (predRow_spec hch hvX).1 with h' | h'
                  · rwa [hpar]
                  · rw [hpar, h'] at hpi
                    exact absurd rfl hpi
              rw [ite_eq_right hne]
              exact hb' hvi hpi
            · -- the site is on the arc
              push Not at hpi
              have hy : siteRow i = v.1 := by
                by_contra hne
                exact (show (parV v).1 i ≠ S₀ i from h₄ _ hyX (hymin _ hvX hvi) hne hyi) hpi
              rw [ite_eq_left hy]
              exact hb hvi hpi
          · push Not at hvi
            have hne : siteRow i ≠ v.1 := by
              intro hy
              rcases hsiteRow i with ⟨-, h₅, -⟩ | ⟨-, h₅, -⟩
              · exact h₅ (hy ▸ hvi)
              · exact h₅ (hy ▸ hvi)
            rw [ite_eq_right hne, hvi]
            by_contra hpi
            exact (h₃ (show (parV v).1 i ≠ S₀ i from fun h' => hpi h'.symm)) hvi
        rcases hvmem with hvA | hvB
        · refine hstep h.chainA hvA (hparA v hvS hvA) fun hvi => ?_
          rcases hsiteRow i with h₁ | ⟨h₁, h₂, -⟩
          · exact h₁
          · exact absurd h₂ (fun h₃ => h₃ (h.disj _ hvA _ h₁ i hvi))
        · refine hstep h.chainB hvB (hparB v hvS hvB) fun hvi => ?_
          rcases hsiteRow i with ⟨h₁, h₂, -⟩ | h₁
          · exact absurd (h.disj _ h₁ _ hvB i h₂) hvi
          · exact h₁
      label_recomb := by
        intro v p q hp hq i
        by_cases hvs : v.1 = s
        · have hvS : v.1 ≠ S₀ := fun h' => h.sS (hvs.symm.trans h')
          simp only [hvS, ite_false, Option.some.injEq] at hp
          simp only [hvs, ite_true, Option.some.injEq] at hq
          have h₁ : q.1 = topRow S₀ B := by rw [← hq]
          have h₂ : p.1 = topRow S₀ A := by rw [← hp]; exact hparS v hvS hvs
          have := h.recomb.multiple i
          rw [hvs, h₂, h₁]
          exact this.symm
        · simp [hvs] at hq }
  have hs : ∀ i, ∃ v, P.site i = some v := fun i => ⟨_, rfl⟩
  have hrec : ∀ x, (P.toNetwork hs).IsRecomb x → x.1 = s := by
    rintro x ⟨e | e, f | f, hef, he, hf⟩
    · exact absurd (congrArg Sum.inl (Subtype.ext (he.trans hf.symm))) hef
    · have hne : P.par₂ x ≠ none := (hf : f.1 = x) ▸ f.2
      by_contra hxs
      exact hne (by simp [P, hxs])
    · have hne : P.par₂ x ≠ none := (he : e.1 = x) ▸ e.2
      by_contra hxs
      exact hne (by simp [P, hxs])
    · have hne : P.par₂ x ≠ none := (he : e.1 = x) ▸ e.2
      by_contra hxs
      exact hne (by simp [P, hxs])
  have hobeysN : (P.toNetwork hs).Obeys c := by
    rw [Network.obeys_iff]
    intro x hx
    have hxs : x.1 = s := hrec x hx
    have hxS : x.1 ≠ S₀ := fun h' => h.sS (hxs.symm.trans h')
    have hq : P.par₂ x ≠ none := by simp [P, hxs]
    have hp : P.par x ≠ none := by simp [P, hxS]
    refine ⟨.inr ⟨x, hq⟩, .inl ⟨x, hp⟩, by simp, rfl, rfl, ?_⟩
    change Recombinant c (((P.par₂ x).get _).1) (((P.par x).get _).1) x.1
    have hg₁ : ((P.par x).get (Option.isSome_iff_ne_none.2 hp)) = parV x := by simp [P, hxS]
    have hg₂ : ((P.par₂ x).get (Option.isSome_iff_ne_none.2 hq)).1 = topRow S₀ B := by simp [P, hxs]
    rw [hg₁, hg₂, hparS x hxS hxs, hxs]
    exact h.recomb
  -- all the rows are nodes
  have hTne : (insert s (A ∪ B)).Nonempty := ⟨s, Finset.mem_insert_self _ _⟩
  have hanc : ∀ r : (insert s (A ∪ B) : Finset (κ → Bool)), ∃ v, (P.toNetwork hs).label v = r.1 := fun r => ⟨⟨r.1, Finset.mem_insert_of_mem r.2⟩, rfl⟩
  choose anchor hanchor using hanc
  have hcov : ∀ i, ∃ r ∈ insert s (A ∪ B), r i ≠ (P.toNetwork hs).label (P.toNetwork hs).root i := fun i => by
    obtain ⟨r, hr, hri⟩ := h.cover i
    exact ⟨r, Finset.mem_insert_of_mem hr, hri⟩
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := (P.toNetwork hs).exists_trim hTne hanchor hcov
  refine ⟨a, b, N', h₁ c hobeysN, h₃, h₂, h₄.trans ?_⟩
  refine Finite.card_le_one_iff_subsingleton.2 ⟨fun x y => ?_⟩
  exact Subtype.ext (Subtype.ext ((hrec _ x.2.1).trans (hrec _ y.2.1).symm))

end Gall

end GusfieldEtAl2004
