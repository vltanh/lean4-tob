module

public import Gusfield2007.Components
public import Gusfield2007.ExplicitNetworks
public import Gusfield2007.Histories
public import Gusfield2007.SufficientConditions
public import Gusfield2007.Parsimony

/-!
# Gusfield et al. 2007: the statements around Theorem 10 and line 425

* **Theorem 10 without an ancestral sequence.** `theorem10` holds in each crossover model with no hypothesis on the columns, through the labels of a tight network on two sites with different columns (`exists_row_of_eq_haplotypeBound`). The same step gives the
  unrooted form, `minDecomposable_of_haplotypeBound_eq`.
* **Theorem 10 as printed**, with the unrooted count `R(M + S)`, is false for single crossovers: `theorem10Printed_single_false`, on fourteen rows and eight sites. Its lower bounds are by `lt_RS_single_of_closed`. It holds when the tight root differs from `S` in at most one
  component, in both models: `sMinDecomposable_of_tight_root`, by `RS_restrict_gap_le`. For multiple crossovers, `Gusfield2007.Theorem10PrintedMultiple` has a counterexample, given one computation that the kernel hasn't completed.
* **Line 425**, `MinDecomposableOfForallS`, is open. What's proved is its reduction to roots, `minDecomposable_iff_exists_root`, and the case `H(M) = R(M)`, `minDecomposableOfForallS_of_haplotypeBound_eq`.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [Finite ι] {V E : Type*}

variable [LinearOrder ι]

/-- **Theorem 10 without an ancestral sequence** (`g:thm10_unrooted`). If `H(M) = R(M)` then `M` is min decomposable, and if `H(M) = R¹(M)` then `M` is min-1 decomposable, with or without identical columns. An optimal network's root doesn't merge components, since on two sites with different columns its label is a
pair of a row, and two sites with one column don't conflict. It isn't in the paper, whose Theorem 10 is rooted. -/
theorem minDecomposable_of_haplotypeBound_eq {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound M = R c M) : MinDecomposable c M := by
  obtain ⟨a, b, N, hc, hd, hcount⟩ := Nat.sInf_mem (recombSet_nonempty c hM)
  have hcount' : N.recombCount = R c M := hcount
  have hH : (N.recombCount : ℤ) = haplotypeBound M := by rw [h, hcount']
  have hT : ∀ r ∈ M, ∃ v, N.label v = r := hd.displays
  have hadj : ∀ i j, Conflict N.ancestral M i j → (incompatGraph M).Reachable i j := by
    intro i j hij
    by_cases hcol : columnOf M i = columnOf M j
    · have hval : ∀ r ∈ M, r i = r j := fun r hr => congrFun hcol ⟨r, hr⟩
      by_cases hS : N.ancestral i = false ∧ N.ancestral j = true
      · obtain ⟨r, hr, h₁, h₂⟩ := hij true false (Or.inl (by rw [hS.1]; decide))
        rw [hval r hr, h₂] at h₁
        exact absurd h₁ (by decide)
      · obtain ⟨r, hr, h₁, h₂⟩ := hij false true (by
          by_contra hcon
          push Not at hcon
          exact hS ⟨hcon.1.symm, hcon.2.symm⟩)
        rw [hval r hr, h₂] at h₁
        exact absurd h₁ (by decide)
    · obtain ⟨r, hr, h₁, h₂⟩ := exists_row_of_eq_haplotypeBound N hT hH hcol N.root
      refine SimpleGraph.Adj.reachable (fun x y => ?_)
      by_cases hxy : x = N.label N.root i ∧ y = N.label N.root j
      · exact ⟨r, hr, h₁.trans hxy.1.symm, h₂.trans hxy.2.symm⟩
      · exact hij x y (by
          by_contra hcon
          push Not at hcon
          exact hxy hcon)
  have hreach : ∀ i j, (conflictGraph N.ancestral M).Reachable i j ↔ (incompatGraph M).Reachable i j := by
    intro i j
    constructor
    · intro hr
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => exact SimpleGraph.Reachable.refl _
      | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
    · exact SimpleGraph.Reachable.mono fun a b (hab : Incompatible M a b) x y _ => hab x y
  have hsum := Network.sum_RS_le_recombCount (G := incompatGraph M) hc hd hC fun x hx C C' hb hb' => by
    by_contra hne
    exact breaksAt_unique_of_eq_haplotypeBound N hT hH hx hne hb hb'
  obtain ⟨a', b', N', h₁, h₂, h₃, h₄, h₅⟩ := theorem3 c M N.ancestral hM hC
  rw [finsum_connectedComponent_congr hreach (fun s => RS c (s.domRestrict N.ancestral) (restrictRows s M))] at h₅
  have hle : R c M ≤ N'.recombCount := Nat.sInf_le ⟨a', b', N', h₁, h₂, rfl⟩
  exact ⟨a', b', N', h₁, h₂, h₄.of_reachable_iff hreach, le_antisymm (by omega) hle⟩

/-- **Line 425, by roots** (`g:line425_roots`). When `M` is S-min decomposable for all `S`, it's min decomposable exactly when some optimal root doesn't merge components of `G(M)`. So `MinDecomposableOfForallS` says that, under its hypothesis, some optimal root doesn't merge. -/
theorem minDecomposable_iff_exists_root {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty) (hall : ∀ S, SMinDecomposable c S M) :
    MinDecomposable c M ↔ ∃ S, RS c S M = R c M ∧ ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j := by
  constructor
  · rintro ⟨a, b, N, h₁, h₂, h₃, h₄⟩
    refine ⟨N.ancestral, le_antisymm ?_ (R_le_RS c _ hM), reachable_conflictGraph_iff h₂ h₃⟩
    rw [← h₄]
    exact RS_le_recombCount N h₁ h₂ rfl
  · rintro ⟨S, hS, hG⟩
    exact minDecomposable_of_sMinDecomposable (hall S) hS hG

/-- **Line 425 when the haplotype bound is tight** (`g:line425_tight`). `MinDecomposableOfForallS` holds when `H(M) = R(M)`, without its hypothesis being used. -/
theorem minDecomposableOfForallS_of_haplotypeBound_eq {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound M = R c M) : MinDecomposableOfForallS c M := fun _ =>
  minDecomposable_of_haplotypeBound_eq hM hC h

/-! ### A lower bound for single crossovers, by a closed set of rows -/

section ClosedSet

variable {κ : Type*} [LinearOrder κ]

/-- A site off the sites used has the root's state. -/
theorem Gen.eq_of_notMem {c : Crossover} {S : κ → Bool} {A : Finset (κ → Bool)} {U : Set κ} {r : ℕ} (h : Gen c S A U r) :
    ∀ p ∈ A, ∀ i, i ∉ U → p i = S i := by
  induction h with
  | base =>
    intro p hp i _
    rw [Finset.mem_singleton.1 hp]
  | @flip A U r p q j _ hp _ hflip ih =>
    intro t ht i hi
    have hij : i ≠ j := fun h => hi (h ▸ Set.mem_insert _ _)
    have hiU : i ∉ U := fun h => hi (Set.mem_insert_of_mem _ h)
    rcases Finset.mem_insert.1 ht with rfl | ht
    · rw [hflip.2 i hij]
      exact ih p hp i hiU
    · exact ih t ht i hiU
  | @recomb A U r p p' q _ hp hp' hm ih =>
    intro t ht i hi
    rcases Finset.mem_insert.1 ht with rfl | ht
    · rcases hm.multiple i with h' | h'
      · rw [h']
        exact ih p hp i hi
      · rw [h']
        exact ih p' hp' i hi
    · exact ih t ht i hi

/-- A history inside `L` stays inside `K`, if `K` contains the root and is closed under what a single-crossover history can do inside `L`: change a site still at the root's state, and recombine. -/
theorem Gen.subset_of_closed {S : κ → Bool} {A : Finset (κ → Bool)} {U : Set κ} {r : ℕ} (h : Gen .single S A U r)
    {K L : Finset (κ → Bool)} (hS : S ∈ K)
    (hf : ∀ p ∈ K, ∀ i, ∀ q ∈ L, IsFlip i p q → p i = S i → q ∈ K)
    (hm : ∀ p ∈ K, ∀ p' ∈ K, ∀ q ∈ L, Recombinant .single p p' q → q ∈ K)
    (hA : A ⊆ L) : A ⊆ K := by
  induction h with
  | base => exact Finset.singleton_subset_iff.2 hS
  | @flip A U r p q i hg hp hi hflip ih =>
    have hAL : A ⊆ L := (Finset.subset_insert _ _).trans hA
    have hAK := ih hAL
    exact Finset.insert_subset (hf p (hAK hp) i q (hA (Finset.mem_insert_self _ _)) hflip (hg.eq_of_notMem p hp i hi)) hAK
  | @recomb A U r p p' q _ hp hp' hrec ih =>
    have hAL : A ⊆ L := (Finset.subset_insert _ _).trans hA
    have hAK := ih hAL
    exact Finset.insert_subset (hm p (hAK hp) p' (hAK hp') q (hA (Finset.mem_insert_self _ _)) hrec) hAK

variable {m : ℕ}

/-- A lower set of `Fin m` is an initial segment. -/
theorem exists_prefix_of_lowerSet (L : LowerSet (Fin m)) : ∃ n : Fin (m + 1), ∀ i : Fin m, i ∈ L ↔ i.val < n.val := by
  by_cases hall : ∀ i : Fin m, i ∈ L
  · exact ⟨⟨m, Nat.lt_succ_self m⟩, fun i => ⟨fun _ => i.2, fun _ => hall i⟩⟩
  · push Not at hall
    have hex : ∃ k, ∃ h : k < m, (⟨k, h⟩ : Fin m) ∉ L := by
      obtain ⟨i, hi⟩ := hall
      exact ⟨i.val, i.2, hi⟩
    obtain ⟨hk, hnot⟩ := Nat.find_spec hex
    refine ⟨⟨Nat.find hex, Nat.lt_succ_of_lt hk⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · by_contra hlt
      exact hnot (L.lower (show (⟨Nat.find hex, hk⟩ : Fin m) ≤ i from not_lt.1 hlt) hi)
    · by_contra hi'
      exact Nat.find_min hex hi ⟨i.2, hi'⟩

/-- **A lower bound on `R¹_S`, by a closed set of rows.** If `S` is a row, and `M` has `1 + m + b` rows, a network with at most `b` recombination nodes has no other labels, and they are generated from `S` one at a time. If a set `K` of rows contains `S`, is closed under the steps
of such a history, and misses a row of `M`, there is no such network. -/
theorem lt_RS_single_of_closed {S : Fin m → Bool} {M K : Finset (Fin m → Bool)} {b : ℕ} (hSM : S ∈ M)
    (hcard : M.card = 1 + m + b) (hS : S ∈ K)
    (hf : ∀ p ∈ K, ∀ i, ∀ q ∈ M, IsFlip i p q → p i = S i → q ∈ K)
    (hm : ∀ p ∈ K, ∀ p' ∈ K, ∀ q ∈ M, ∀ n : Fin (m + 1), (∀ i : Fin m, (i.val < n.val → q i = p i) ∧ (n.val ≤ i.val → q i = p' i)) → q ∈ K)
    (hmiss : ∃ r ∈ M, r ∉ K) : b < RS .single S M := by
  by_contra hle
  obtain ⟨a', b', N, hc, hd, hS', hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .single S ⟨S, hSM⟩)
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hc
  have hcount' : N.recombCount = RS .single S M := hcount
  rw [hS', hcount'] at hg
  have hsub : M ⊆ A := fun r hr => by
    obtain ⟨v, rfl⟩ := hd.displays r hr
    exact hlab v
  have hU : U.ncard ≤ m := by
    have := Set.ncard_le_ncard (Set.subset_univ U)
    simpa [Set.ncard_univ] using this
  have hA := hg.card_le
  have heq : M = A := Finset.eq_of_subset_of_card_le hsub (by omega)
  obtain ⟨r, hr, hrK⟩ := hmiss
  refine hrK (hg.subset_of_closed hS hf (fun p hp p' hp' q hq hrec => ?_) heq.ge (hsub hr))
  obtain ⟨Ls, hLs⟩ := hrec
  obtain ⟨n, hn⟩ := exists_prefix_of_lowerSet Ls
  refine hm p hp p' hp' q hq n fun i => ⟨fun hi => ?_, fun hi => ?_⟩
  · rw [hLs i, ite_eq_left ((hn i).2 hi)]
  · rw [hLs i, ite_eq_right fun h => absurd ((hn i).1 h) (not_lt.2 hi)]

end ClosedSet

/-! ### Theorem 10 as printed, when the tight root differs from `S` in one component -/

section OneComponent

variable {κ : Type*} [LinearOrder κ] {c : Crossover}

omit [Finite ι] [LinearOrder ι] in
/-- A restricted flip, in any crossover model: a flip if the site is kept, and nothing otherwise. -/
theorem Gen.comp_flip_of {f : κ → ι} (hf : Function.Injective f) {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ}
    (h : Gen c (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r) {p q : ι → Bool} {i : ι} (hp : p ∈ A) (hi : i ∉ U) (hflip : IsFlip i p q) :
    Gen c (S ∘ f) ((insert q A).image (· ∘ f)) (f ⁻¹' insert i U) r := by
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

omit [Finite ι] in
/-- Restricting a history to some sites, in a crossover model that restriction keeps. -/
theorem Gen.restrict_of {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} (h : Gen c S A U r) {f : κ → ι}
    (hf : Function.Injective f) (hc : ∀ p p' q, Recombinant c p p' q → Recombinant c (p ∘ f) (p' ∘ f) (q ∘ f)) :
    ∃ r' ≤ r, Gen c (S ∘ f) (A.image (· ∘ f)) (f ⁻¹' U) r' := by
  induction h with
  | base => exact ⟨0, le_rfl, by simpa using Gen.base⟩
  | flip _ hp hi hflip ih =>
    obtain ⟨r', hle, hg⟩ := ih
    exact ⟨r', hle, hg.comp_flip_of hf hp hi hflip⟩
  | @recomb A U r p p' q _ hp hp' hm ih =>
    obtain ⟨r', hle, hg⟩ := ih
    refine ⟨r' + 1, by omega, ?_⟩
    rw [Finset.image_insert]
    exact hg.recomb (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hp') (hc p p' q hm)

omit [Finite ι] in
/-- Single crossovers stay so on a set of sites with the order of `ι`. -/
theorem recombinant_comp_of_strictMono {f : κ → ι} (hf : StrictMono f) (hc : c = .single ∨ c = .multiple) (p p' q : ι → Bool) (h : Recombinant c p p' q) :
    Recombinant c (p ∘ f) (p' ∘ f) (q ∘ f) := by
  rcases hc with rfl | rfl
  · obtain ⟨L, hL⟩ := h
    refine ⟨⟨f ⁻¹' L, fun a b hba ha => L.lower (hf.monotone hba) ha⟩, fun i => ?_⟩
    have h₁ := hL (f i)
    by_cases hi : f i ∈ L
    · have hi' : i ∈ (⟨f ⁻¹' L, fun a b hba ha => L.lower (hf.monotone hba) ha⟩ : LowerSet κ) := hi
      simp only [Function.comp_apply, hi, hi', ↓reduceIte] at h₁ ⊢
      exact h₁
    · have hi' : i ∉ (⟨f ⁻¹' L, fun a b hba ha => L.lower (hf.monotone hba) ha⟩ : LowerSet κ) := hi
      simp only [Function.comp_apply, hi, hi', ↓reduceIte] at h₁ ⊢
      exact h₁
  · exact fun i => h (f i)

/-- A history without a recombinant that is already a label: then each step adds one label. -/
theorem Gen.exists_card_eq {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {r : ℕ} (h : Gen c S A U r) :
    ∃ r' ≤ r, Gen c S A U r' ∧ A.card = 1 + U.ncard + r' := by
  induction h with
  | base => exact ⟨0, le_rfl, .base, by simp⟩
  | @flip A U r p q i hg hp hi hflip ih =>
    obtain ⟨r', hle, hg', hcard⟩ := ih
    refine ⟨r', hle, hg'.flip hp hi hflip, ?_⟩
    have hq : q ∉ A := fun hq => by
      have h₁ := hg.eq_of_notMem q hq i hi
      have h₂ := hg.eq_of_notMem p hp i hi
      rw [hflip.1, h₂] at h₁
      simp at h₁
    rw [Finset.card_insert_of_notMem hq, Set.ncard_insert_of_notMem hi (Set.toFinite U), hcard]
    omega
  | @recomb A U r p p' q _ hp hp' hm ih =>
    obtain ⟨r', hle, hg', hcard⟩ := ih
    by_cases hq : q ∈ A
    · rw [Finset.insert_eq_of_mem hq]
      exact ⟨r', by omega, hg', hcard⟩
    · refine ⟨r' + 1, by omega, hg'.recomb hp hp' hm, ?_⟩
      rw [Finset.card_insert_of_notMem hq, hcard]
      omega

omit [Finite ι] in
/-- **A history is a `PreNet`**, in any crossover model. It's `Gen.exists_preNet`, for recombinations modelling mutations, with the same proof. -/
theorem Gen.exists_preNet_of {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {k : ℕ} (h : Gen c S A U k) :
    ∃ (V : Type) (_ : Finite V) (P : PreNet ι V), P.label P.root = S ∧ (∀ s ∈ A, ∃ v, P.label v = s) ∧ (∀ i, i ∈ U ↔ ∃ v, P.site i = some v) ∧
      (∀ x p q, P.par x = some p → P.par₂ x = some q → Recombinant c (P.label q) (P.label p) (P.label x)) ∧ P.recombCount ≤ k := by
  induction h with
  | base =>
    refine ⟨Unit, inferInstance, ⟨(), fun _ => none, fun _ => none, fun _ => none, fun _ => S, by simp, rfl, by simp, ?_, by simp, by simp, by simp⟩, rfl, ?_, by simp, by simp, ?_⟩
    · intro v h
      obtain ⟨_, -, h'⟩ := Relation.TransGen.tail'_iff.1 h
      simp at h'
    · intro s hs
      exact ⟨(), (Finset.mem_singleton.1 hs).symm⟩
    · simp [PreNet.recombCount]
  | @flip A U k s q i hd hs hi hf ih =>
    obtain rfl := hf.eq_ite
    obtain ⟨V, _, P, h₁, h₂, h₃, h₄, h₅⟩ := ih
    obtain ⟨v, rfl⟩ := h₂ s hs
    have hsite : P.site i = none := by
      by_contra hne
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
      exact hi ((h₃ i).2 ⟨w, hw⟩)
    refine ⟨Option V, inferInstance, P.extend v none (fun j => if j = i then !P.label v j else P.label v j) (fun j => j = i) (fun j hj => hj ▸ hsite) (by simp)
      (fun _ j => by by_cases hj : j = i <;> simp [hj]), h₁, ?_, ?_, ?_, (P.recombCount_extend_none _ _ _ _ _ _).trans h₅⟩
    · intro s' hs'
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact ⟨none, rfl⟩
      · obtain ⟨w, rfl⟩ := h₂ s' hs'
        exact ⟨some w, rfl⟩
    · intro i'
      simp only [PreNet.extend]
      by_cases hii : i' = i
      · simp [hii]
      · simp only [Set.mem_insert_iff, hii, false_or, ↓reduceIte, h₃ i', Option.map_eq_some_iff]
        constructor
        · rintro ⟨w, hw⟩
          exact ⟨some w, w, hw, rfl⟩
        · rintro ⟨_, w, hw, -⟩
          exact ⟨w, hw⟩
    · rintro (- | x) p q hp hq
      · simp [PreNet.extend] at hq
      · simp only [PreNet.extend, Option.map_eq_some_iff] at hp hq
        obtain ⟨p', hp', rfl⟩ := hp
        obtain ⟨q', hq', rfl⟩ := hq
        exact h₄ x p' q' hp' hq'
  | @recomb A U k s t q' hd hs ht hm ih =>
    obtain ⟨V, _, P, h₁, h₂, h₃, h₄, h₅⟩ := ih
    by_cases hdone : q' ∈ A
    · rw [Finset.insert_eq_of_mem hdone]
      exact ⟨V, inferInstance, P, h₁, h₂, h₃, h₄, h₅.trans (Nat.le_succ k)⟩
    · have hst : s ≠ t := by
        rintro rfl
        refine hdone ?_
        have : q' = s := funext fun i => by
          rcases hm.multiple i with h' | h' <;> exact h'
        rw [this]
        exact hs
      obtain ⟨v, rfl⟩ := h₂ s hs
      obtain ⟨w, rfl⟩ := h₂ t ht
      have hvw : v ≠ w := fun h' => hst (by rw [h'])
      refine ⟨Option V, inferInstance, P.extend w (some v) q' (fun _ => False) (fun _ h' => h'.elim) ?_ (by simp), h₁, ?_, ?_, ?_,
        (P.recombCount_extend_some _ _ _ _ _ _ _).trans (Nat.add_le_add_right h₅ 1)⟩
      · rintro q₀ hq₀
        obtain rfl := Option.some_inj.1 hq₀
        refine ⟨hvw, fun i => ?_, fun _ h' => h'⟩
        rcases hm.multiple i with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      · intro s' hs'
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact ⟨none, rfl⟩
        · obtain ⟨u, rfl⟩ := h₂ s' hs'
          exact ⟨some u, rfl⟩
      · intro i'
        simp only [PreNet.extend, ↓reduceIte, h₃ i', Option.map_eq_some_iff]
        constructor
        · rintro ⟨u, hu⟩
          exact ⟨some u, u, hu, rfl⟩
        · rintro ⟨_, u, hu, -⟩
          exact ⟨u, hu⟩
      · rintro (- | x) p q hp hq
        · simp only [PreNet.extend, Option.some.injEq, Option.map_some] at hp hq
          subst hp hq
          exact hm
        · simp only [PreNet.extend, Option.map_eq_some_iff] at hp hq
          obtain ⟨p', hp', rfl⟩ := hp
          obtain ⟨q', hq', rfl⟩ := hq
          exact h₄ x p' q' hp' hq'

omit [Finite ι] in
/-- A history gives a network: `R_S(M)` is at most the number of recombinations of a history from `S` whose labels contain `M`. -/
theorem Gen.RS_le_of_subset {S : ι → Bool} {A M : Finset (ι → Bool)} {U : Set ι} {k : ℕ} (h : Gen c S A U k) (hMA : M ⊆ A) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    RS c S M ≤ k := by
  obtain ⟨V, _, P, h₁, h₂, h₃, h₄, h₅⟩ := h.exists_preNet_of
  have hs : ∀ i, ∃ v, P.site i = some v := fun i => by
    refine (h₃ i).1 ?_
    by_contra hi
    obtain ⟨r, hr, r', hr', hne⟩ := hC i
    exact hne ((h.eq_of_notMem r (hMA hr) i hi).trans (h.eq_of_notMem r' (hMA hr') i hi).symm)
  obtain ⟨a, b, N, hc, hd, hS, hle⟩ := P.exists_network hs h₄ hM hC fun r hr => h₂ r (hMA hr)
  exact (Nat.sInf_le ⟨a, b, N, hc, hd, hS.trans h₁, rfl⟩ : RS c S M ≤ _).trans (hle.trans h₅)

omit [Finite ι] in
/-- All the sites are used, in a history whose labels contain rows with no constant column. -/
theorem Gen.ncard_eq_of_noConstantColumn {S : ι → Bool} {A M : Finset (ι → Bool)} {U : Set ι} {k : ℕ} (h : Gen c S A U k) (hMA : M ⊆ A) (hC : NoConstantColumn M) :
    U.ncard = Nat.card ι := by
  have hU : U = Set.univ := Set.eq_univ_of_forall fun i => by
    by_contra hi
    obtain ⟨r, hr, r', hr', hne⟩ := hC i
    exact hne ((h.eq_of_notMem r (hMA hr) i hi).trans (h.eq_of_notMem r' (hMA hr') i hi).symm)
  rw [hU, Set.ncard_univ]

/-- **The count on one set of sites.** A history from `S` whose labels `A` contain `M` gives, on the sites of `C`, a network for `M(C)` with one recombination node for each label on `C` beyond the root and the sites: labels that agree on `C` count once. -/
theorem Gen.RS_restrict_add_le {S : ι → Bool} {A M : Finset (ι → Bool)} {U : Set ι} {k : ℕ} (hc : c = .single ∨ c = .multiple) (h : Gen c S A U k) (hMA : M ⊆ A) (hM : M.Nonempty) (hC : NoConstantColumn M) (C : Set ι) :
    RS c (C.domRestrict S) (restrictRows C M) + Nat.card C + 1 ≤ (A.image C.domRestrict).card := by
  have hval : StrictMono (Subtype.val : C → ι) := fun _ _ hab => hab
  obtain ⟨r', -, hg⟩ := h.restrict_of Subtype.val_injective (recombinant_comp_of_strictMono hval hc)
  change Gen c (C.domRestrict S) (A.image C.domRestrict) (Subtype.val ⁻¹' U) r' at hg
  obtain ⟨r'', -, hg', hcard⟩ := hg.exists_card_eq
  have hsub : restrictRows C M ⊆ A.image C.domRestrict := Finset.image_subset_image hMA
  have hne : (restrictRows C M).Nonempty := hM.image _
  have hle := hg'.RS_le_of_subset hsub hne (hC.restrictRows C)
  have hn := hg'.ncard_eq_of_noConstantColumn hsub (hC.restrictRows C)
  omega

/-- **The gap to the haplotype bound doesn't grow on restricting the sites** (`g:gap_restrict`). In the single-crossover and multiple-crossover models, with `T = M + S`, for each set of sites `C`:
`R_{S(C)}(M(C)) − (|T(C)| − |C| − 1) ≤ R_S(M) − (|T| − m − 1)`. With distinct columns, the two brackets are the haplotype bounds. It isn't in the paper. -/
theorem RS_restrict_gap_le (hc : c = .single ∨ c = .multiple) {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M) (C : Set ι) :
    (RS c (C.domRestrict S) (restrictRows C M) : ℤ) + Nat.card C + 1 ≤ (restrictRows C (addRow M S)).card + RS c S M + Nat.card ι + 1 - (addRow M S).card := by
  obtain ⟨a, b, N, hN, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S hM)
  obtain ⟨A, U, hg, hlab⟩ := N.exists_gen hN
  have hcount' : N.recombCount = RS c S M := hcount
  rw [hS, hcount'] at hg
  have hMA : M ⊆ A := fun r hr => by
    obtain ⟨v, rfl⟩ := hd.displays r hr
    exact hlab v
  have hT : addRow M S ⊆ A := fun r hr => by
    rcases mem_addRow.1 hr with rfl | hr
    · exact hg.root_mem
    · exact hMA hr
  have h₁ := hg.RS_restrict_add_le hc hMA hM hC C
  have h₂ := hg.card_le
  rw [hg.ncard_eq_of_noConstantColumn hMA hC] at h₂
  have hsplit : (A.image C.domRestrict).card ≤ (restrictRows C (addRow M S)).card + (A \ addRow M S).card := by
    have : A = addRow M S ∪ (A \ addRow M S) := (Finset.union_sdiff_of_subset hT).symm
    conv_lhs => rw [this, Finset.image_union]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have hsd := Finset.card_sdiff_of_subset hT
  have hle := Finset.card_le_card hT
  omega

/-- **Theorem 10 as printed, when the tight root differs from `S` in at most one component** (`g:thm10_printed_one_component`). Let the columns of `M + S` be distinct, in the single-crossover or multiple-crossover model, and let `S'` have `H(M + S) = R_{S'}(M + S)`: when
`H(M + S) = R(M + S)`, that's any root of an optimal network for `M + S`. If `S'` and `S` agree outside one component of `G_S(M)`, then `M` is S-min decomposable.

The other components are tight at `S`, because they are tight at `S'`, and the excess of the one left over the haplotype bound is at most that of `M + S` (`RS_restrict_gap_le`). `theorem10Printed_single_false` shows that for single crossovers this can't be extended to two components. -/
theorem sMinDecomposable_of_tight_root (hc : c = .single ∨ c = .multiple) {M : Finset (ι → Bool)} {S S' : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hinj : Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (htight : haplotypeBound (addRow M S) = RS c S' (addRow M S))
    (C₀ : (conflictGraph S M).ConnectedComponent) (hagree : ∀ i, i ∉ C₀.supp → S' i = S i) : SMinDecomposable c S M := by
  have hMT : M ⊆ addRow M S := fun r hr => mem_addRow.2 (Or.inr hr)
  have hTne : (addRow M S).Nonempty := hM.mono hMT
  have hCT := hC.addRow S
  -- The network at `S'` has the rows as its labels.
  obtain ⟨a', b', N', hc', hd', hS', hcount'⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S' hTne)
  obtain ⟨A', U', hg', hlab'⟩ := N'.exists_gen hc'
  have hcount'' : N'.recombCount = RS c S' (addRow M S) := hcount'
  rw [hS', hcount''] at hg'
  have hTA' : addRow M S ⊆ A' := fun r hr => by
    obtain ⟨v, rfl⟩ := hd'.displays r hr
    exact hlab' v
  have hdist : distinctColumns (addRow M S) = Nat.card ι := by
    rw [distinctColumns, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  have hH : haplotypeBound (addRow M S) = ((addRow M S).card : ℤ) - Nat.card ι - 1 := by
    rw [haplotypeBound, hdist]
  have hA'card := hg'.card_le
  rw [hg'.ncard_eq_of_noConstantColumn hTA' hCT] at hA'card
  have hA' : addRow M S = A' := Finset.eq_of_subset_of_card_le hTA' (by omega)
  have hS'T : S' ∈ addRow M S := hA' ▸ hg'.root_mem
  have hadd : addRow (addRow M S) S' = addRow M S := addRow_eq_of_mem hS'T
  -- `M + S` is S'-min decomposable.
  have hdec : SMinDecomposable c S' (addRow M S) := theorem10 hTne hCT (by rw [hadd]; exact htight)
  have heq := (sMinDecomposable_iff c (addRow M S) S' hTne hCT).1 hdec
  have hG' : conflictGraph S' (addRow M S) = conflictGraph S M := by
    rw [conflictGraph_eq_incompatGraph_addRow S' (addRow M S), hadd, ← conflictGraph_eq_incompatGraph_addRow S M]
  rw [hG'] at heq
  have : Finite (conflictGraph S M).ConnectedComponent := Quot.finite _
  have := Fintype.ofFinite (conflictGraph S M).ConnectedComponent
  rw [finsum_eq_sum_of_fintype] at heq
  -- The three bounds on the components.
  let g : (conflictGraph S M).ConnectedComponent → ℤ := fun C => ((restrictRows C.supp (addRow M S)).card : ℤ) - Nat.card C.supp - 1
  have h₁ : ∀ C, g C ≤ (RS c (C.supp.domRestrict S') (restrictRows C.supp (addRow M S)) : ℤ) := by
    intro C
    have hne : (restrictRows C.supp (addRow M S)).Nonempty := hTne.image _
    have hb := MyersGriffiths2003.haplotypeBound_addRow_le_RS c (C.supp.domRestrict S') (restrictRows C.supp (addRow M S)) hne
    rw [addRow_eq_of_mem (mem_restrictRows.2 ⟨S', hS'T, rfl⟩)] at hb
    have hdc : distinctColumns (restrictRows C.supp (addRow M S)) ≤ Nat.card C.supp := by
      rw [distinctColumns, ← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by rw [Set.ncard_univ])
    unfold haplotypeBound at hb
    change ((restrictRows C.supp (addRow M S)).card : ℤ) - Nat.card C.supp - 1 ≤ _
    omega
  have h₂ : ∀ C, C ≠ C₀ → (RS c (C.supp.domRestrict S) (restrictRows C.supp M) : ℤ) ≤ g C := by
    intro C hne
    have hS'S : C.supp.domRestrict S' = C.supp.domRestrict S := by
      funext x
      refine hagree x.1 fun hx => hne ?_
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex x.2 hx
    have hb := hg'.RS_restrict_add_le hc (hMT.trans hTA') hM hC C.supp
    rw [← hA', hS'S] at hb
    change RS c (C.supp.domRestrict S) (restrictRows C.supp M) + Nat.card C.supp + 1 ≤ (restrictRows C.supp (addRow M S)).card at hb
    change _ ≤ ((restrictRows C.supp (addRow M S)).card : ℤ) - Nat.card C.supp - 1
    omega
  have h₃ := RS_restrict_gap_le hc hM hC C₀.supp (S := S)
  set E : ℤ := (RS c S M : ℤ) + Nat.card ι + 1 - (addRow M S).card with hE
  have h₃' : (RS c (C₀.supp.domRestrict S) (restrictRows C₀.supp M) : ℤ) ≤ g C₀ + E := by
    change _ ≤ ((restrictRows C₀.supp (addRow M S)).card : ℤ) - Nat.card C₀.supp - 1 + E
    rw [hE]
    omega
  have hsum : (∑ C : (conflictGraph S M).ConnectedComponent, (RS c (C.supp.domRestrict S) (restrictRows C.supp M) : ℤ)) ≤ ∑ C : (conflictGraph S M).ConnectedComponent, (g C + if C = C₀ then E else 0) := by
    refine Finset.sum_le_sum fun C _ => ?_
    by_cases hCC : C = C₀
    · subst hCC
      simpa using h₃'
    · simpa [hCC] using h₂ C hCC
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ C₀, ite_eq_left (Finset.mem_univ _)] at hsum
  have hg_le : (∑ C : (conflictGraph S M).ConnectedComponent, g C) ≤ ∑ C : (conflictGraph S M).ConnectedComponent, (RS c (C.supp.domRestrict S') (restrictRows C.supp (addRow M S)) : ℤ) :=
    Finset.sum_le_sum fun C _ => h₁ C
  have hcast : (∑ C : (conflictGraph S M).ConnectedComponent, (RS c (C.supp.domRestrict S') (restrictRows C.supp (addRow M S)) : ℤ)) = (RS c S' (addRow M S) : ℤ) := by
    rw [heq]
    push_cast
    rfl
  have hfinal : (∑ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M)) ≤ RS c S M := by
    have : ((∑ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) : ℕ) : ℤ) ≤ RS c S M := by
      push_cast
      rw [hE] at hsum
      rw [hH] at htight
      omega
    exact_mod_cast this
  refine (sMinDecomposable_iff c M S hM hC).2 ?_
  rw [finsum_eq_sum_of_fintype]
  refine le_antisymm ?_ hfinal
  obtain ⟨a, b, N, h₁', h₂', h₃', -, h₅'⟩ := theorem3 c M S hM hC
  rw [finsum_eq_sum_of_fintype] at h₅'
  exact (RS_le_recombCount N h₁' h₂' h₃').trans h₅'.le

end OneComponent

/-! ### Theorem 10 as printed is false for single crossovers -/

section Printed

/-- Fourteen rows on eight sites: a counterexample to Theorem 10 as printed, for single crossovers. The sites `0, 1, 4, 5` are one component and `2, 3, 6, 7` the other. -/
def printedRows : Finset (Fin 8 → Bool) :=
  {ofBits [0, 0, 0, 0, 0, 0, 0, 0], ofBits [0, 0, 1, 0, 0, 0, 0, 0], ofBits [0, 0, 0, 1, 0, 0, 0, 0], ofBits [0, 0, 1, 0, 0, 0, 1, 0],
   ofBits [0, 0, 1, 1, 0, 0, 1, 0], ofBits [1, 0, 1, 1, 0, 0, 1, 0], ofBits [0, 1, 1, 1, 0, 0, 1, 0], ofBits [1, 0, 1, 1, 1, 0, 1, 0],
   ofBits [1, 1, 1, 1, 1, 0, 1, 0], ofBits [0, 1, 1, 1, 0, 1, 1, 0], ofBits [1, 1, 1, 1, 0, 1, 1, 0], ofBits [1, 0, 1, 1, 1, 1, 1, 0],
   ofBits [0, 0, 0, 1, 0, 0, 0, 1], ofBits [0, 0, 1, 1, 0, 0, 0, 1]}

/-- The ancestral sequence of the counterexample: one of the rows. -/
def printedRoot : Fin 8 → Bool := ofBits [1, 1, 1, 1, 1, 0, 1, 0]

/-- A network for `printedRows` with the root `00000000` and five single crossovers. -/
def printedTightNet : NetSpec 8 26 30 :=
  ⟨[0, 0, 1, 2, 1, 4, 5, 3, 6, 6, 7, 8, 7, 10, 9, 10, 11, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
   [1, 2, 3, 4, 5, 5, 6, 6, 7, 8, 9, 10, 11, 11, 12, 12, 13, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
   [8, 9, 0, 1, 10, 11, 2, 3],
   [0, 4, 8, 68, 136, 140, 76, 77, 78, 93, 110, 111, 125, 95, 0, 4, 8, 68, 136, 140, 76, 77, 78, 93, 110, 111]⟩

theorem printedTightNet_valid : printedTightNet.Valid := by decide +kernel

theorem printedTightNet_single : printedTightNet.SingleCheck := by decide +kernel

theorem printedTightNet_recombs : printedTightNet.recombs = 5 := by decide +kernel

/-- A network for `printedRows` with the root `printedRoot` and six single crossovers. Its one label off the rows, `11110000`, is a crossover of the root and of the row `00100000`. -/
def printedRootNet : NetSpec 8 27 32 :=
  ⟨[0, 1, 2, 3, 4, 0, 5, 5, 7, 6, 1, 6, 9, 7, 10, 11, 4, 8, 5, 13, 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13],
   [1, 2, 3, 4, 5, 6, 6, 7, 8, 8, 9, 10, 10, 11, 11, 12, 12, 13, 14, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26],
   [2, 0, 7, 3, 1, 10, 4, 17],
   [95, 93, 77, 76, 68, 4, 15, 0, 8, 125, 111, 110, 78, 136, 140, 95, 93, 77, 76, 68, 4, 0, 8, 125, 111, 110, 136]⟩

theorem printedRootNet_valid : printedRootNet.Valid := by decide +kernel

theorem printedRootNet_single : printedRootNet.SingleCheck := by decide +kernel

theorem printedRootNet_recombs : printedRootNet.recombs = 6 := by decide +kernel

theorem printedRows_nonempty : printedRows.Nonempty := ⟨ofBits [0, 0, 0, 0, 0, 0, 0, 0], by decide +kernel⟩

theorem printedRows_noConstantColumn : NoConstantColumn printedRows := by
  unfold NoConstantColumn
  decide +kernel

theorem printedRoot_mem : printedRoot ∈ printedRows := by decide +kernel

theorem addRow_printedRows : addRow printedRows printedRoot = printedRows := addRow_eq_of_mem printedRoot_mem

theorem haplotypeBound_printedRows : haplotypeBound printedRows = 5 := by
  have hcard : printedRows.card = 14 := by decide +kernel
  have hinj : Function.Injective fun i : Fin 8 => fun r : printedRows => (r : Fin 8 → Bool) i := by
    intro i j hij
    have h : ∀ r ∈ printedRows, r i = r j := fun r hr => congrFun hij ⟨r, hr⟩
    revert h
    revert i j
    decide +kernel
  have hcols : distinctColumns printedRows = 8 := by
    rw [distinctColumns, Set.ncard_range_of_injective hinj]
    simp
  simp [haplotypeBound, hcard, hcols]

theorem R_printedRows : R .single printedRows = 5 := by
  have hle : R .single printedRows ≤ 5 := by
    rw [← printedTightNet_recombs]
    exact NetSpec.R_le printedTightNet_valid (by decide +kernel) (NetSpec.obeys_single_toNetwork _ printedTightNet_single)
  have hge := MyersGriffiths2003.haplotypeBound_le_R .single printedRows printedRows_nonempty
  rw [haplotypeBound_printedRows] at hge
  omega

theorem RS_printedRows_le : RS .single printedRoot printedRows ≤ 6 := by
  rw [← printedRootNet_recombs]
  exact NetSpec.RS_le printedRootNet_valid (by decide +kernel) (NetSpec.obeys_single_toNetwork _ printedRootNet_single) (by decide +kernel)

/-- The first component: the sites `0, 1, 4, 5`. -/
def printedC₁ : Set (Fin 8) := {i | i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5}

/-- The sites of the first component, in order. -/
def printedSites₁ : Fin 4 → Fin 8 := fun a => Fin.ofNat 8 ([0, 1, 4, 5].getD a 0)

/-- The sites of the second component, in order. -/
def printedSites₂ : Fin 4 → Fin 8 := fun a => Fin.ofNat 8 ([2, 3, 6, 7].getD a 0)

theorem printedSites₁_strictMono : StrictMono printedSites₁ := fun a b h => by
  revert a b
  decide

theorem printedSites₂_strictMono : StrictMono printedSites₂ := fun a b h => by
  revert a b
  decide

theorem printedSites₁_range : Set.range printedSites₁ = printedC₁ := Set.ext fun i => by
  change (∃ a, printedSites₁ a = i) ↔ (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5)
  revert i
  decide

theorem printedSites₂_range : Set.range printedSites₂ = printedC₁ᶜ := Set.ext fun i => by
  change (∃ a, printedSites₂ a = i) ↔ ¬ (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5)
  revert i
  decide

theorem printed_conflictGraph : conflictGraph printedRoot printedRows = incompatGraph printedRows := by
  rw [conflictGraph_eq_incompatGraph_addRow, addRow_printedRows]

theorem printed_reachable (i j : Fin 8) : (incompatGraph printedRows).Reachable i j ↔ (i ∈ printedC₁ ↔ j ∈ printedC₁) := by
  refine reachable_iff_of_adj _ (fun i j hij => ?_) (a := 1) (b := 2) (fun i hi => reachable_of_two_steps ?_) (fun i hi => reachable_of_two_steps ?_) i j
  · change Incompatible printedRows i j at hij
    change (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5) ↔ (j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5)
    unfold Incompatible at hij
    revert hij
    revert i j
    decide +kernel
  · change i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 at hi
    change i = 1 ∨ Incompatible printedRows i 1 ∨ ∃ k, Incompatible printedRows i k ∧ Incompatible printedRows k 1
    unfold Incompatible
    revert hi
    revert i
    decide +kernel
  · change ¬ (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5) at hi
    change i = 2 ∨ Incompatible printedRows i 2 ∨ ∃ k, Incompatible printedRows i k ∧ Incompatible printedRows k 2
    unfold Incompatible
    revert hi
    revert i
    decide +kernel

/-- `R¹_{S(C₁)}(M(C₁)) ≥ 4`: from the root `1110`, the rows `0100, 0101, 1101` can't be reached with no other label. -/
theorem four_le_RS_printed₁ : 4 ≤ RS .single (printedC₁.domRestrict printedRoot) (restrictRows printedC₁ printedRows) := by
  rw [RS_restrictRows printedSites₁ printedSites₁_strictMono printedSites₁_range]
  have := lt_RS_single_of_closed (S := printedRoot ∘ printedSites₁) (M := printedRows.image fun r => r ∘ printedSites₁) (b := 3)
    (K := {ofBits [1, 1, 1, 0], ofBits [1, 0, 1, 0], ofBits [1, 0, 0, 0], ofBits [0, 0, 0, 0], ofBits [1, 0, 1, 1]})
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold IsFlip; decide +kernel) (by decide +kernel) (by decide +kernel)
  omega

/-- `R¹_{S(C₂)}(M(C₂)) ≥ 3`: from the root `1110`, the rows `0100, 0101, 1101` can't be reached with no other label. -/
theorem three_le_RS_printed₂ : 3 ≤ RS .single (printedC₁ᶜ.domRestrict printedRoot) (restrictRows printedC₁ᶜ printedRows) := by
  rw [RS_restrictRows printedSites₂ printedSites₂_strictMono printedSites₂_range]
  have := lt_RS_single_of_closed (S := printedRoot ∘ printedSites₂) (M := printedRows.image fun r => r ∘ printedSites₂) (b := 2)
    (K := {ofBits [1, 1, 1, 0], ofBits [1, 0, 1, 0], ofBits [1, 0, 0, 0], ofBits [0, 0, 0, 0]})
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold IsFlip; decide +kernel) (by decide +kernel) (by decide +kernel)
  omega

/-- The sum over the components of `G_S(M)`, for the counterexample. -/
theorem seven_le_sum_printed : 7 ≤ ∑ᶠ C : (conflictGraph printedRoot printedRows).ConnectedComponent,
    RS .single (C.supp.domRestrict printedRoot) (restrictRows C.supp printedRows) := by
  have hreach : ∀ i j, (conflictGraph printedRoot printedRows).Reachable i j ↔ (i ∈ printedC₁ ↔ j ∈ printedC₁) := by
    rw [printed_conflictGraph]
    exact printed_reachable
  have e := finsum_connectedComponent_eq_add hreach (a := 1) (b := 2) (Or.inr (Or.inl rfl)) (by
    change ¬ ((2 : Fin 8) = 0 ∨ (2 : Fin 8) = 1 ∨ (2 : Fin 8) = 4 ∨ (2 : Fin 8) = 5)
    decide) fun C => RS .single (C.domRestrict printedRoot) (restrictRows C printedRows)
  rw [e]
  have h₁ := four_le_RS_printed₁
  have h₂ := three_le_RS_printed₂
  omega

/-- `printedRows` is min-1 decomposable, though not S-min-1 decomposable for its row `printedRoot`. -/
theorem minDecomposable_printedRows : MinDecomposable .single printedRows :=
  minDecomposable_of_haplotypeBound_eq printedRows_nonempty printedRows_noConstantColumn (by
    rw [haplotypeBound_printedRows, R_printedRows]
    rfl)

/-- **Theorem 10 as printed is false for single crossovers** (`g:thm10_printed_false`). "If `H(M + S) = R¹(M + S)` then `M` is S-min-1 decomposable" (line 568) fails on `printedRows`, with `S = printedRoot`, a row, and with the columns of `M + S` distinct: `H(M + S) = R¹(M + S) = 5`,
the root `00000000` being tight, while `R¹_S(M) = 6` and the two components of `G_S(M)` need at least `4` and `3` recombination nodes for their sequences at `S`. This is a counterexample to the printed statement only: with the rooted count, the statement is `theorem10`, which is what the proof
of the paper is about. -/
theorem theorem10Printed_single_false : printedRows.Nonempty ∧ NoConstantColumn printedRows ∧
    haplotypeBound (addRow printedRows printedRoot) = R .single (addRow printedRows printedRoot) ∧
    RS .single printedRoot printedRows = 6 ∧ ¬ SMinDecomposable .single printedRoot printedRows ∧
    ¬ Theorem10Printed .single printedRows printedRoot := by
  have hH : haplotypeBound (addRow printedRows printedRoot) = R .single (addRow printedRows printedRoot) := by
    rw [addRow_printedRows, haplotypeBound_printedRows, R_printedRows]
    rfl
  have hnot : ¬ SMinDecomposable .single printedRoot printedRows := by
    intro h
    have heq := (sMinDecomposable_iff .single printedRows printedRoot printedRows_nonempty printedRows_noConstantColumn).1 h
    have h₁ := seven_le_sum_printed
    have h₂ := RS_printedRows_le
    omega
  have hge : (5 : ℤ) ≤ RS .single printedRoot printedRows := by
    have := MyersGriffiths2003.haplotypeBound_addRow_le_RS .single printedRoot printedRows printedRows_nonempty
    rwa [addRow_printedRows, haplotypeBound_printedRows] at this
  have hne : (5 : ℤ) ≠ RS .single printedRoot printedRows := by
    intro h5
    refine hnot (theorem10 printedRows_nonempty printedRows_noConstantColumn ?_)
    rw [addRow_printedRows, haplotypeBound_printedRows]
    exact h5
  have hle := RS_printedRows_le
  refine ⟨printedRows_nonempty, printedRows_noConstantColumn, hH, by omega, hnot, fun h => hnot (h hH)⟩

end Printed

end Gusfield2007
