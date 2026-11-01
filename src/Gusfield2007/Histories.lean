module

public import Gusfield2007.Basic

/-!
# Gusfield et al. 2007: the labels of a network, generated one at a time

A tool for the lower bounds on `R` of Section 5, which the paper obtains by running programs (beagle, multicross.pl; lines 404, 612), and for going from a tree to a network in Section 4.1 (`Gusfield2007.Parsimony`). It isn't in the paper.

A network gives a *history*, `Gen`: starting from the ancestral sequence, the labels appear one at a time, each one either a copy of an earlier label with one fresh site changed, or a
recombinant of two earlier labels, and that counts one recombination. So there are at most `1 + m + R` labels (`Gen.card_le`), which is the count behind the haplotype bound of line 559. And the
labels can be generated from the root inside themselves: a set containing the root and closed under the two steps, inside the labels, contains all of them (`Gen.mem_of_closed`). This second fact
is what `Gusfield2007.LabelSearch` checks by computation.

`Gen.split` is the composite bound on `R¹` of Myers and Griffiths 2003 (pp. 376-377, eqs. 1, 2), in the form that we need: the sites to the left of a point and the sites to the right of it can't be broken by the same single crossover. Checked against the source: see its docstring.

Nothing here counts arcs or vertices, so that these arguments don't need the structure of the network again once `Network.exists_gen` has been applied.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u v w

section Gen

variable {ι : Type u}

/-- `q` is `p` with the state of the site `i` changed. -/
def IsFlip (i : ι) (p q : ι → Bool) : Prop :=
  q i = !p i ∧ ∀ j, j ≠ i → q j = p j

variable [LinearOrder ι]

/-- The sequence with the state of `i` changed is unique. -/
theorem IsFlip.eq_ite {i : ι} {p q : ι → Bool} (h : IsFlip i p q) : q = fun j => if j = i then !p j else p j := by
  funext j
  by_cases hj : j = i
  · subst hj
    simpa using h.1
  · simpa [hj] using h.2 j hj

/-- A history: `Gen c S A U r` says that the labels `A` can be generated from the root `S` using the sites `U`, each once, and `r` recombinations. -/
inductive Gen (c : Crossover) (S : ι → Bool) : Finset (ι → Bool) → Set ι → ℕ → Prop
  | base : Gen c S {S} ∅ 0
  | flip {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} {p q : ι → Bool} {i : ι} :
      Gen c S A U r → p ∈ A → i ∉ U → IsFlip i p q → Gen c S (insert q A) (insert i U) r
  | recomb {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} {p p' q : ι → Bool} :
      Gen c S A U r → p ∈ A → p' ∈ A → Recombinant c p p' q → Gen c S (insert q A) U (r + 1)

variable {c : Crossover} {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ}

/-- A multiple-crossover history, forgetting the model. -/
theorem Gen.toMultiple (h : Gen c S A U r) : Gen .multiple S A U r := by
  induction h with
  | base => exact .base
  | flip _ hp hi hf ih => exact .flip ih hp hi hf
  | recomb _ hp hp' hm ih => exact .recomb ih hp hp' hm.multiple

/-- The root is one of the labels. -/
theorem Gen.root_mem (h : Gen c S A U r) : S ∈ A := by
  induction h with
  | base => simp
  | flip _ _ _ _ ih => exact Finset.mem_insert_of_mem ih
  | recomb _ _ _ _ ih => exact Finset.mem_insert_of_mem ih

/-- The count behind the haplotype bound (line 559): a label is the root's, or it uses a new site, or it's a recombinant. -/
theorem Gen.card_le [Finite ι] (h : Gen c S A U r) : A.card ≤ 1 + U.ncard + r := by
  induction h with
  | base => simp
  | @flip A U r p q i _ _ hi _ ih =>
    have h₁ := Finset.card_insert_le q A
    have h₂ : (insert i U).ncard = U.ncard + 1 := Set.ncard_insert_of_notMem hi (Set.toFinite U)
    omega
  | @recomb A U r p p' q _ _ _ _ ih =>
    have h₁ := Finset.card_insert_le q A
    omega

/-- A site that has changed has a label off the root's state. -/
theorem Gen.exists_ne (h : Gen c S A U r) : ∀ i ∈ U, ∃ t ∈ A, t i ≠ S i := by
  induction h with
  | base => simp
  | @flip A U r p q i _ hp _ hf ih =>
    intro i' hi'
    rcases hi' with rfl | hi'
    · by_cases hpi : p i' = S i'
      · exact ⟨q, Finset.mem_insert_self _ _, by rw [hf.1, hpi]; simp⟩
      · exact ⟨p, Finset.mem_insert_of_mem hp, hpi⟩
    · obtain ⟨t, ht, hne⟩ := ih i' hi'
      exact ⟨t, Finset.mem_insert_of_mem ht, hne⟩
  | recomb _ _ _ _ ih =>
    intro i' hi'
    obtain ⟨t, ht, hne⟩ := ih i' hi'
    exact ⟨t, Finset.mem_insert_of_mem ht, hne⟩

/-- A set containing the root, and closed under the two steps inside `Y`, contains the labels of any history inside `Y`. -/
theorem Gen.mem_of_closed (h : Gen c S A U r) {X : Set (ι → Bool)} {Y : Finset (ι → Bool)} (hAY : A ⊆ Y) (hS : S ∈ X)
    (hf : ∀ i p q, p ∈ X → q ∈ Y → IsFlip i p q → q ∈ X)
    (hm : ∀ p p' q, p ∈ X → p' ∈ X → q ∈ Y → Recombinant .multiple p p' q → q ∈ X) : ∀ a ∈ A, a ∈ X := by
  induction h with
  | base =>
    intro a ha
    rw [Finset.mem_singleton.1 ha]
    exact hS
  | @flip A U r p q i _ hp _ hflip ih =>
    have hA : A ⊆ Y := (Finset.subset_insert _ _).trans hAY
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hf i p a (ih hA p hp) (hAY (Finset.mem_insert_self _ _)) hflip
    · exact ih hA a ha
  | @recomb A U r p p' q _ hp hp' hmix ih =>
    have hA : A ⊆ Y := (Finset.subset_insert _ _).trans hAY
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hm p p' a (ih hA p hp) (ih hA p' hp') (hAY (Finset.mem_insert_self _ _)) hmix.multiple
    · exact ih hA a ha

/-- Changing one more site is a flip. -/
theorem isFlip_iteFlip (T : Finset ι) (p : ι → Bool) (i : ι) (hi : i ∉ T) :
    IsFlip i (fun j => if j ∈ T then !p j else p j) (fun j => if j ∈ insert i T then !p j else p j) := by
  refine ⟨by simp [hi], fun j hj => ?_⟩
  simp [Finset.mem_insert, hj]

/-- Changing the sites of `T` one at a time: the arc of a network with several sites. -/
theorem Gen.flips (h : Gen c S A U r) {p : ι → Bool} (hp : p ∈ A) (T : Finset ι) (hT : ∀ i ∈ T, i ∉ U) :
    ∃ A' : Finset (ι → Bool), A ⊆ A' ∧ Gen c S A' (U ∪ (T : Set ι)) r ∧ (fun j => if j ∈ T then !p j else p j) ∈ A' := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨A, subset_rfl, by simpa using h, by simpa using hp⟩
  | insert i T hi ih =>
    obtain ⟨A', hsub, hg, hmem⟩ := ih fun j hj => hT j (Finset.mem_insert_of_mem hj)
    have hiU : i ∉ U ∪ (T : Set ι) := by
      simpa [hi] using hT i (Finset.mem_insert_self _ _)
    refine ⟨_, hsub.trans (Finset.subset_insert _ _), ?_, Finset.mem_insert_self _ _⟩
    have := hg.flip hmem hiU (isFlip_iteFlip T p i hi)
    have hU : insert i (U ∪ (T : Set ι)) = U ∪ ((insert i T : Finset ι) : Set ι) := by
      ext j
      simp only [Set.mem_insert_iff, Set.mem_union, Finset.coe_insert, Finset.mem_coe]
      tauto
    rwa [hU] at this

/-! ### The history of a network -/

variable {V : Type v} {E : Type w}

/-- The labels of a closed set of nodes `P` containing the root can be generated with a recombination for each recombination node in `P`. -/
theorem Network.exists_gen_of_closed [Finite ι] [Finite V] (N : Network ι V E) (hc : N.Obeys c) (n : ℕ) :
    ∀ P : Finset V, P.card = n → N.root ∈ P → (∀ e, N.tgt e ∈ P → N.src e ∈ P) →
      ∃ (A : Finset (ι → Bool)) (U : Set ι), Gen c N.ancestral A U (P.filter N.IsRecomb).card ∧
        (∀ v ∈ P, N.label v ∈ A) ∧ ∀ i ∈ U, N.tgt (N.site i) ∈ P := by
  have hroot : ∀ e, N.tgt e ≠ N.root := (N.root_iff N.root).2 rfl
  induction n with
  | zero =>
    intro P hP hr
    rw [Finset.card_eq_zero] at hP
    rw [hP] at hr
    exact absurd hr (Finset.notMem_empty _)
  | succ n ih =>
    intro P hP hr hcl
    by_cases hP₁ : P.erase N.root = ∅
    · -- Only the root.
      have hPeq : P = {N.root} := by
        rw [← Finset.insert_erase hr, hP₁]
        rfl
      subst hPeq
      refine ⟨{N.ancestral}, ∅, ?_, ?_, by simp⟩
      · have : (Finset.filter N.IsRecomb {N.root}).card = 0 := by
          simp [Finset.filter_singleton, Network.not_isRecomb_root]
        rw [this]
        exact .base
      · intro v hv
        rw [Finset.mem_singleton.1 hv]
        exact Finset.mem_singleton_self _
    · -- A last node `v` of `P`.
      obtain ⟨v, hv, hmin⟩ := N.wellFounded_transGen_swap.has_min (↑(P.erase N.root) : Set V) (by
        rw [Finset.coe_nonempty, Finset.nonempty_iff_ne_empty]
        exact hP₁)
      have hvP : v ∈ P := Finset.mem_of_mem_erase hv
      have hvr : v ≠ N.root := Finset.ne_of_mem_erase hv
      have hno : ∀ e, N.src e = v → N.tgt e ∉ P := fun e he htP => by
        exact hmin _ (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hroot e, htP⟩)) (Relation.TransGen.single ⟨e, he, rfl⟩)
      have hpar : ∀ e, N.tgt e = v → N.src e ∈ P.erase v := fun e he => by
        refine Finset.mem_erase.2 ⟨fun h => ?_, hcl e (he ▸ hvP)⟩
        exact hno e h (he ▸ hvP)
      obtain ⟨A, U, hg, hlab, hU⟩ := ih (P.erase v) (by rw [Finset.card_erase_of_mem hvP, hP]; rfl)
        (Finset.mem_erase.2 ⟨hvr.symm, hr⟩) (fun e he => by
          have hteP := Finset.mem_of_mem_erase he
          refine Finset.mem_erase.2 ⟨fun h => ?_, hcl e hteP⟩
          exact hno e h hteP)
      have hUP : ∀ i ∈ U, N.tgt (N.site i) ≠ v := fun i hi h => by
        have := hU i hi
        rw [h] at this
        exact Finset.notMem_erase _ _ this
      have hPe : P = insert v (P.erase v) := (Finset.insert_erase hvP).symm
      by_cases hrec : N.IsRecomb v
      · -- A recombination node.
        have hcard : (P.filter N.IsRecomb).card = ((P.erase v).filter N.IsRecomb).card + 1 := by
          conv_lhs => rw [hPe]
          rw [Finset.filter_insert]
          simp only [hrec, ↓reduceIte]
          rw [Finset.card_insert_of_notMem]
          exact fun h => Finset.notMem_erase _ _ (Finset.mem_of_mem_filter _ h)
        obtain ⟨e, f, -, he, hf, hm⟩ := (N.obeys_iff c).1 hc v hrec
        refine ⟨insert (N.label v) A, U, ?_, ?_, ?_⟩
        · rw [hcard]
          exact hg.recomb (hlab _ (hpar e he)) (hlab _ (hpar f hf)) hm
        · intro w hw
          by_cases hwv : w = v
          · rw [hwv]
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hlab w (Finset.mem_erase.2 ⟨hwv, hw⟩))
        · exact fun i hi => Finset.mem_of_mem_erase (hU i hi)
      · -- A node with one incoming arc.
        have hcard : (P.filter N.IsRecomb).card = ((P.erase v).filter N.IsRecomb).card := by
          conv_lhs => rw [hPe]
          rw [Finset.filter_insert]
          simp only [hrec, ↓reduceIte]
        obtain ⟨e, he⟩ : ∃ e, N.tgt e = v := by
          by_contra hne
          push Not at hne
          exact hvr ((N.root_iff v).1 hne)
        have huniq : ∀ f, N.tgt f = N.tgt e → f = e := fun f hf => by
          by_contra hne
          exact hrec ⟨f, e, hne, hf.trans he, he⟩
        have : Fintype ι := Fintype.ofFinite ι
        obtain ⟨A', hsub, hg', hmem⟩ := hg.flips (hlab _ (hpar e he)) (Finset.univ.filter fun i => N.site i = e)
          (fun i hi hiU => by
            have hi' : N.site i = e := (Finset.mem_filter.1 hi).2
            exact hUP i hiU (by rw [hi', he]))
        have hlabel : N.label v = fun j => if j ∈ Finset.univ.filter (fun i => N.site i = e) then !N.label (N.src e) j
            else N.label (N.src e) j := by
          funext i
          have := N.label_tree e huniq i
          rw [he] at this
          rw [this]
          simp
        refine ⟨A', _, hcard ▸ hg', ?_, ?_⟩
        · intro w hw
          by_cases hwv : w = v
          · rw [hwv, hlabel]
            exact hmem
          · exact hsub (hlab w (Finset.mem_erase.2 ⟨hwv, hw⟩))
        · rintro i (hi | hi)
          · exact Finset.mem_of_mem_erase (hU i hi)
          · have hi' : N.site i = e := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
            rw [hi', he]
            exact hvP

/-- **The history of a network.** The labels of the nodes of a network can be generated from its root, using one recombination for each recombination node. -/
theorem Network.exists_gen [Finite ι] [Finite V] (N : Network ι V E) (hc : N.Obeys c) :
    ∃ (A : Finset (ι → Bool)) (U : Set ι), Gen c N.ancestral A U N.recombCount ∧ ∀ v, N.label v ∈ A := by
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨A, U, hg, hlab, -⟩ := N.exists_gen_of_closed hc _ Finset.univ rfl (Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
  have hcount : N.recombCount = (Finset.univ.filter N.IsRecomb).card :=
    Nat.subtype_card _ fun x => by simp
  exact ⟨A, U, hcount ▸ hg, fun v => hlab v (Finset.mem_univ _)⟩

/-! ### Restricting a history to some of its sites -/

section Restrict

variable {κ : Type*} [LinearOrder κ]

omit [LinearOrder ι] in
/-- A restricted flip: a flip if the site is kept, and nothing otherwise. -/
theorem Gen.comp_flip {f : κ → ι} (hf : Function.Injective f) {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ}
    (h : Gen .multiple (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r) {p q : ι → Bool} {i : ι} (hp : p ∈ A) (hi : i ∉ U) (hflip : IsFlip i p q) :
    Gen .multiple (S ∘ f) ((insert q A).image (· ∘ f)) (f ⁻¹' insert i U) r := by
  have hp' : p ∘ f ∈ A.image (· ∘ f) := Finset.mem_image_of_mem _ hp
  rw [Finset.image_insert]
  by_cases hrange : ∃ a, f a = i
  · obtain ⟨a, rfl⟩ := hrange
    have hflip' : IsFlip a (p ∘ f) (q ∘ f) :=
      ⟨hflip.1, fun b hb => hflip.2 (f b) fun hfb => hb (hf hfb)⟩
    have hU : f ⁻¹' insert (f a) U = insert a (f ⁻¹' U) := by
      ext b
      simp [hf.eq_iff]
    rw [hU]
    exact h.flip hp' hi hflip'
  · have hq : q ∘ f = p ∘ f := by
      funext a
      exact hflip.2 (f a) fun hfa => hrange ⟨a, hfa⟩
    have hU : f ⁻¹' insert i U = f ⁻¹' U := by
      ext b
      simp only [Set.mem_preimage, Set.mem_insert_iff, or_iff_right_iff_imp]
      exact fun hb => absurd ⟨b, hb⟩ hrange
    rw [hU, hq, Finset.insert_eq_of_mem hp']
    exact h

/-- Restricting a multiple-crossover history to some of its sites: `R(M(I)) ≤ R(M)`. -/
theorem Gen.restrict {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} (h : Gen .multiple S A U r) {f : κ → ι}
    (hf : Function.Injective f) : ∃ r' ≤ r, Gen .multiple (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r' := by
  induction h with
  | base => exact ⟨0, le_rfl, by simpa using Gen.base⟩
  | flip _ hp hi hflip ih =>
    obtain ⟨r', hle, hg⟩ := ih
    exact ⟨r', hle, hg.comp_flip hf hp hi hflip⟩
  | @recomb A U r p p' q _ hp hp' hm ih =>
    obtain ⟨r', hle, hg⟩ := ih
    refine ⟨r' + 1, by omega, ?_⟩
    rw [Finset.image_insert]
    exact hg.recomb (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp') fun a => hm (f a)

/-- **The composite bound** of Myers and Griffiths, for two sets of sites, the first to the left of the second; they can share a site. A single crossover falls on one side, so it's a
recombination for at most one of them: `R¹(M) ≥ R(M(I)) + R(M(J))`.

Checked against Myers and Griffiths 2003, pp. 376-377. They let `r_l` be the number of recombination events in the interval between consecutive sites, and combine local bounds `B_ij` on a region by the constraints `Σ_{l=i}^{j-1} r_l ≥ B_ij` of (1), (2). Two such constraints, on regions that share at most an endpoint, add up to
`Σ r_l ≥ B + B'`. This is that instance, with `B = R(M(I))` and `B' = R(M(J))`, proved directly on a history rather than through the `r_l`. Their assumption that each event has "exactly one endpoint" in the region is `Gen .single`. Their integer program for many regions and their Algorithm 1 are in `External.MyersGriffiths2003.Algorithm1`, and the bound on `R¹` is `MyersGriffiths2003.algorithm1_le_R` in `External.MyersGriffiths2003.Composite`, with `MyersGriffiths2003.add_R_le_R` for two intervals, keeping single crossovers on both. `I` and `J` needn't be intervals, which is covered by their remark that a
bound can be taken on any subset of the sites of a region (p. 379). -/
theorem Gen.split {κ' : Type*} [LinearOrder κ'] {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} (h : Gen .single S A U r)
    {f : κ → ι} {g : κ' → ι} (hf : StrictMono f) (hg : StrictMono g) (hfg : ∀ a b, f a ≤ g b) :
    ∃ r₁ r₂, r₁ + r₂ ≤ r ∧ Gen .multiple (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r₁ ∧
      Gen .multiple (S ∘ g) (A.image (· ∘ g)) (g ⁻¹' U) r₂ := by
  induction h with
  | base => exact ⟨0, 0, le_rfl, by simpa using Gen.base, by simpa using Gen.base⟩
  | flip _ hp hi hflip ih =>
    obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := ih
    exact ⟨r₁, r₂, hle, h₁.comp_flip hf.injective hp hi hflip, h₂.comp_flip hg.injective hp hi hflip⟩
  | @recomb A U r p p' q _ hp hp' hm ih =>
    obtain ⟨r₁, r₂, hle, h₁, h₂⟩ := ih
    have hmm : Recombinant .multiple p p' q := hm.multiple
    obtain ⟨L, hL⟩ := hm
    by_cases hcut : ∃ a, f a ∉ L
    · -- The crossover is to the left of `g`, which copies `p'`.
      obtain ⟨a, ha⟩ := hcut
      have hq : q ∘ g = p' ∘ g := by
        funext b
        have hb : g b ∉ L := fun hb => ha (L.lower (hfg a b) hb)
        change q (g b) = p' (g b)
        simp [hL, hb]
      refine ⟨r₁ + 1, r₂, by omega, ?_, ?_⟩
      · rw [Finset.image_insert]
        exact h₁.recomb (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp') fun a => hmm (f a)
      · have hmem : p' ∘ g ∈ A.image (· ∘ g) := Finset.mem_image_of_mem _ hp'
        rw [Finset.image_insert, hq, Finset.insert_eq_of_mem hmem]
        exact h₂
    · -- All of `f` is on the left of the crossover, and copies `p`.
      push Not at hcut
      have hq : q ∘ f = p ∘ f := by
        funext a
        change q (f a) = p (f a)
        simp [hL, hcut a]
      refine ⟨r₁, r₂ + 1, by omega, ?_, ?_⟩
      · have hmem : p ∘ f ∈ A.image (· ∘ f) := Finset.mem_image_of_mem _ hp
        rw [Finset.image_insert, hq, Finset.insert_eq_of_mem hmem]
        exact h₁
      · rw [Finset.image_insert]
        exact h₂.recomb (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp') fun a => hmm (g a)

end Restrict

end Gen

end Gusfield2007
