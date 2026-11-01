module

public import External.HudsonKaplan1985.AlgorithmBound
public import External.MyersGriffiths2003.Algorithm1
public import External.MyersGriffiths2003.Bound
public import Gusfield2007.Examples

/-!
# The composite bound of Myers and Griffiths

See the `README.md` of this directory. Myers and Griffiths 2003, p. 377: with `r_l` the number of recombination events between the sites `l` and `l + 1`, and `B_ij` "a local bound on the number of recombinations in the region `(s_i, s_j)`", the events of any history satisfy the system (2). So the optimal value of the program, computed by Algorithm 1 (`External.MyersGriffiths2003.Algorithm1`), is a lower bound on the number of recombinations.

The source's assumption that "for every recombination event within it, exactly one endpoint lies within the region and the other outside" is single crossover, `R¹`.

In this module:

* `Network.breakCount`: the number of recombination nodes of a network that break some set of sites. A recombination node breaks a region only if its crossover is in that region, and this is what "the number of events in the region" comes to: `exists_feasible`;
* `IsLocalBounds`: `B_ij` is a local bound, for all networks;
* `algorithm1_le_R`, `algorithm1_le_RS`: **the composite bound**. The second is the case of known ancestral types: "adding an all-zero type to the top of our list of sequences and then proceeding as if types were unknown";
* `isLocalBounds_region`, `R_restrictRows_le_breakCount`: the local bound can be `R¹` of the region itself, which needs `NoConstantColumn`: the source's sites are segregating;
* `isLocalBounds_fourGamete`, `isLocalBounds_haplotypeBounds`: the local bounds of the four-gamete test, which give `R_m`, and of the haplotype bound (4) on subsets of a region with its end points, which give `R_h`;
* `add_R_le_R`: two regions sharing at most an end point. This keeps the single crossovers on both regions, unlike `Gusfield2007.Gen.split`, which has them only on the whole, and it holds for intervals of sites.

The bound `R_s` is in `External.MyersGriffiths2003.SampleHistory`, Proposition 2 in `External.MyersGriffiths2003.Proposition2`, Lemma 4 and Corollary 5 in `External.MyersGriffiths2003.Implementation`, and the constraints such as `r_k = 0` in `External.MyersGriffiths2003.Constraints`.
-/

@[expose] public section

namespace MyersGriffiths2003

open Gusfield2007 Gusfield2007.Network

universe u v w

/-! ### The local bounds as computed from a sample -/

section Compute

variable {S : ℕ}

/-- The sites between `i` and `j`, with both. -/
def region (S i j : ℕ) : Set (Fin S) := {a | i ≤ a.val ∧ a.val ≤ j}

/-- The number of types of `M` at the sites `T`: `H` of (4), for that subset of the sites. -/
def typeCount (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : ℕ :=
  (M.image fun r a => decide (a ∈ T) && r a).card

/-- The bound (4) on the subset `T` of the sites, in the case of unknown ancestral types: `H - S' - 1`, where it "will give a negative answer, leading to a zero bound". -/
def haplotypeAt (M : Finset (Fin S → Bool)) (T : Finset (Fin S)) : ℕ := typeCount M T - T.card - 1

/-- `T` is a subset of the sites "with the same endpoint sites as" the region `(i, j)`. -/
def HasEndpoints (i j : ℕ) (T : Finset (Fin S)) : Prop :=
  (∃ a ∈ T, a.val = i) ∧ (∃ b ∈ T, b.val = j) ∧ ∀ c ∈ T, i ≤ c.val ∧ c.val ≤ j

instance (i j : ℕ) : DecidablePred (HasEndpoints (S := S) i j) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- "For a given local region, the best 'haplotype bound' is the maximum bound obtained from applying (4) to subsets with the same endpoint sites as that region." -/
def haplotypeBounds (M : Finset (Fin S → Bool)) : ℕ → ℕ → ℕ := fun i j =>
  ((Finset.univ : Finset (Finset (Fin S))).filter (HasEndpoints i j)).sup (haplotypeAt M)

/-- **`R_m`** (`ext:mg_rm`): Algorithm 1 on the four-gamete test. -/
def Rm (M : Finset (Fin S → Bool)) : ℕ := algorithm1 (HudsonKaplan1985.incompatBounds (HudsonKaplan1985.fourGamete M)) S 0 (S - 1)

/-- **`R_h`** (`ext:mg_rh`): Algorithm 1 on the haplotype bounds, with all subsets: the source's parameters limit the subsets, to save time, which can only lower the bound. -/
def Rh (M : Finset (Fin S → Bool)) : ℕ := algorithm1 (haplotypeBounds M) S 0 (S - 1)

/-- The sample of the source's example, p. 381: the sequences `a, ..., h`. -/
def exampleSample : Finset (Fin 4 → Bool) :=
  {ofBits [0, 0, 0, 0], ofBits [0, 1, 0, 1], ofBits [1, 1, 0, 0], ofBits [0, 1, 1, 0],
    ofBits [1, 1, 1, 1], ofBits [1, 1, 0, 1], ofBits [1, 1, 1, 0], ofBits [1, 0, 0, 1]}

/-- **The example of the source, from its sample** (`ext:mg_example_sample`). The matrices `B^I` and `B^H` of (5) are what the local bounds compute, and `R_m = 2`, `R_h = 3`. -/
theorem exampleSample_values :
    (∀ i j : Fin 4, i < j → HudsonKaplan1985.incompatBounds (HudsonKaplan1985.fourGamete exampleSample) i j = exampleBI i j) ∧
      (∀ i j : Fin 4, i < j → haplotypeBounds exampleSample i j = exampleBH i j) ∧ Rm exampleSample = 2 ∧ Rh exampleSample = 3 ∧
      HudsonKaplan1985.finalList 4 (HudsonKaplan1985.fourGamete exampleSample) = [(0, 1), (2, 3)] := by
  decide +kernel

end Compute

/-! ### Nodes that break a set of sites -/

open scoped Classical

section BreakCount

variable {ι : Type u} {V : Type v} {E : Type w}

/-- The number of recombination nodes of `N` that break the sites `C`: on `C`, the node is a copy of neither parent. -/
noncomputable def breakCount (N : Network ι V E) (C : Set ι) : ℕ := Nat.card {x // N.IsRecomb x ∧ N.BreaksAt x C}

theorem breaksAt_mono {N : Network ι V E} {x : V} {C C' : Set ι} (h : N.BreaksAt x C) (hC : C ⊆ C') : N.BreaksAt x C' :=
  fun e he heq => h e he (funext fun i => congrFun heq ⟨i.1, hC i.2⟩)

theorem breakCount_mono [Finite V] (N : Network ι V E) {C C' : Set ι} (hC : C ⊆ C') : breakCount N C ≤ breakCount N C' :=
  Nat.card_le_card_of_injective (fun x : {x // N.IsRecomb x ∧ N.BreaksAt x C} => (⟨x.1, x.2.1, breaksAt_mono x.2.2 hC⟩ : {x // N.IsRecomb x ∧ N.BreaksAt x C'}))
    fun _ _ h => Subtype.ext (congrArg (fun z : {x // N.IsRecomb x ∧ N.BreaksAt x C'} => z.1) h)

theorem breakCount_le_recombCount [Finite V] (N : Network ι V E) (C : Set ι) : breakCount N C ≤ N.recombCount :=
  Nat.card_le_card_of_injective (fun x : {x // N.IsRecomb x ∧ N.BreaksAt x C} => (⟨x.1, x.2.1⟩ : {x // N.IsRecomb x}))
    fun _ _ h => Subtype.ext (congrArg (fun z : {x // N.IsRecomb x} => z.1) h)

end BreakCount

/-! ### Removing the recombination nodes that don't break anything -/

section Reduce

variable {ι : Type u} {V : Type v} [LinearOrder ι] [Finite V]

/-- A recombination node that is a copy of a parent can be made an ordinary node, under that parent, keeping the labels: the argument of `Gusfield2007.Network.reattach`. What remains are recombination nodes that break the whole of the sites. -/
theorem exists_reduce (n : ℕ) : ∀ {E : Type w} [Finite E] (N : Network ι V E), N.recombCount = n →
    ∃ (E' : Type w) (_ : Finite E') (N' : Network ι V E'), N'.root = N.root ∧ N'.label = N.label ∧ (∀ c, N.Obeys c → N'.Obeys c) ∧
      ∀ x, N'.IsRecomb x → N.IsRecomb x ∧ N.BreaksAt x Set.univ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ N hn
    by_cases hall : ∀ x, N.IsRecomb x → N.BreaksAt x Set.univ
    · exact ⟨E, inferInstance, N, rfl, rfl, fun _ h => h, fun x hx => ⟨hx, hall x hx⟩⟩
    · push Not at hall
      obtain ⟨x, hx, hb⟩ := hall
      unfold BreaksAt at hb
      push Not at hb
      obtain ⟨e, hex, hl⟩ := hb
      subst hex
      obtain ⟨a, b, hab, ha, hb⟩ := hx
      obtain ⟨f, hef, hf⟩ : ∃ f, e ≠ f ∧ N.tgt e = N.tgt f := by
        by_cases hae : a = e
        · exact ⟨b, fun h => hab (hae.trans h), hb.symm⟩
        · exact ⟨a, fun h => hae h.symm, ha.symm⟩
      have hl' : N.label (N.src e) = N.label (N.tgt e) := by
        funext i
        exact (congrFun hl ⟨i, Set.mem_univ i⟩).symm
      have hy : ¬ N.Reach (N.tgt e) (N.src e) := N.not_reach_tgt_src e
      have hlt := recombCount_reattach_lt (N := N) (hef := hef) (he := hf) (hl := hl') (hy := hy)
      obtain ⟨E', hE', N', h₁, h₂, h₃, h₄⟩ := ih _ (hn ▸ hlt) (N.reattach hef hf hl' hy) rfl
      refine ⟨E', hE', N', h₁, h₂, fun c hc => h₃ c (obeys_reattach hc), fun v hv => ?_⟩
      obtain ⟨hv₁, hv₂⟩ := h₄ v hv
      obtain ⟨hv₃, hv₄⟩ := isRecomb_reattach.1 hv₁
      refine ⟨hv₃, fun g hg => ?_⟩
      have hgf : g ≠ f := by
        rintro rfl
        exact hv₄ (hg.symm.trans hf.symm)
      have hge : g ≠ e := by
        rintro rfl
        exact hv₄ hg.symm
      have := hv₂ ⟨g, hgf⟩ hg
      change Set.univ.domRestrict (N.label v) ≠ Set.univ.domRestrict (N.label (if g = e then N.src e else N.src g)) at this
      rwa [ite_eq_right hge] at this

omit [Finite V] in
/-- On the sites `C`, a single crossover is a single crossover. -/
theorem obeys_liftSites_single {E : Type w} {N : Network ι V E} (C : Set ι) (h : N.Obeys .single) :
    (N.liftSites (Subtype.val : C → ι)).Obeys .single := by
  rw [obeys_iff] at h ⊢
  intro x hx
  obtain ⟨e, f, hef, he, hf, L, hL⟩ := h x hx
  refine ⟨e, f, hef, he, hf, ⟨{a | a.val ∈ L}, fun a b hba ha => L.lower hba ha⟩, fun i => ?_⟩
  exact hL i.val

/-- **The network on a set of sites**, with a recombination node only for each one that breaks these sites, when no column of `M'` is constant. -/
theorem exists_restrict_network {E : Type w} [Finite E] [Finite ι] (N : Network ι V E) (C : Set ι) {M' : Finset (C → Bool)} (hM' : M'.Nonempty)
    (hC : NoConstantColumn M') (hd : ∀ r ∈ M', ∃ v, C.domRestrict (N.label v) = r) :
    ∃ (a b : ℕ) (N'' : Network C (Fin a) (Fin b)), (∀ c, (N.liftSites (Subtype.val : C → ι)).Obeys c → N''.Obeys c) ∧ N''.Derives M' ∧
      N''.ancestral = C.domRestrict N.ancestral ∧ N''.recombCount ≤ breakCount N C := by
  obtain ⟨E', hE', N', h₁, h₂, h₃, h₄⟩ := exists_reduce _ (N.liftSites (Subtype.val : C → ι)) rfl
  obtain ⟨a, b, N'', h₅, h₆, h₇, h₈⟩ := exists_derives_of_displays N' hM' hC (fun r hr => by
    obtain ⟨v, hv⟩ := hd r hr
    refine ⟨v, ?_⟩
    rw [h₂]
    exact hv)
  refine ⟨a, b, N'', fun c hc => h₅ c (h₃ c hc), h₆, ?_, h₈.trans ?_⟩
  · rw [h₇]
    unfold ancestral
    rw [h₁, h₂]
    rfl
  · refine Nat.card_le_card_of_injective (fun x : {x // N'.IsRecomb x} => (⟨x.1, (h₄ x.1 x.2).1, ?_⟩ : {x // N.IsRecomb x ∧ N.BreaksAt x C})) fun x y h => ?_
    · intro e he heq
      refine (h₄ x.1 x.2).2 e he (funext ?_)
      rintro ⟨i, -⟩
      exact congrFun heq i
    · exact Subtype.ext (congrArg (fun z : {x // N.IsRecomb x ∧ N.BreaksAt x C} => z.1) h)

/-- **`R¹` of a set of sites** is at most the number of nodes breaking them, in a network displaying `M`. -/
theorem R_restrictRows_le_breakCount {E : Type w} [Finite E] [Finite ι] (N : Network ι V E) (hc : N.Obeys .single) {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hd : ∀ r ∈ M, ∃ v, N.label v = r) (C : Set ι) : R .single (restrictRows C M) ≤ breakCount N C := by
  have hdisp : ∀ r ∈ restrictRows C M, ∃ v, C.domRestrict (N.label v) = r := fun r hr => by
    obtain ⟨ρ, hρ, rfl⟩ := mem_restrictRows.1 hr
    obtain ⟨v, rfl⟩ := hd ρ hρ
    exact ⟨v, rfl⟩
  obtain ⟨a, b, N'', h₁, h₂, -, h₃⟩ := exists_restrict_network N C (hM.image _) (hC.restrictRows C) hdisp
  have hle : R .single (restrictRows C M) ≤ N''.recombCount := Nat.sInf_le ⟨a, b, N'', h₁ _ (obeys_liftSites_single C hc), h₂, rfl⟩
  exact hle.trans h₃

/-- The same with multiple crossovers: nothing to check on the crossovers. -/
theorem R_multiple_restrictRows_le_breakCount {E : Type w} [Finite E] [Finite ι] (N : Network ι V E) {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hd : ∀ r ∈ M, ∃ v, N.label v = r) (C : Set ι) : R .multiple (restrictRows C M) ≤ breakCount N C := by
  have hdisp : ∀ r ∈ restrictRows C M, ∃ v, C.domRestrict (N.label v) = r := fun r hr => by
    obtain ⟨ρ, hρ, rfl⟩ := mem_restrictRows.1 hr
    obtain ⟨v, rfl⟩ := hd ρ hρ
    exact ⟨v, rfl⟩
  obtain ⟨a, b, N'', h₁, h₂, -, h₃⟩ := exists_restrict_network N C (hM.image _) (hC.restrictRows C) hdisp
  have hle : R .multiple (restrictRows C M) ≤ N''.recombCount := Nat.sInf_le ⟨a, b, N'', h₁ _ trivial, h₂, rfl⟩
  exact hle.trans h₃

/-- **`R¹_S` of a set of sites**, with the ancestral sequence restricted to them. -/
theorem RS_restrictRows_le_breakCount {E : Type w} [Finite E] [Finite ι] (N : Network ι V E) (hc : N.Obeys .single) {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hd : ∀ r ∈ M, ∃ v, N.label v = r) (C : Set ι) : RS .single (C.domRestrict N.ancestral) (restrictRows C M) ≤ breakCount N C := by
  have hdisp : ∀ r ∈ restrictRows C M, ∃ v, C.domRestrict (N.label v) = r := fun r hr => by
    obtain ⟨ρ, hρ, rfl⟩ := mem_restrictRows.1 hr
    obtain ⟨v, rfl⟩ := hd ρ hρ
    exact ⟨v, rfl⟩
  obtain ⟨a, b, N'', h₁, h₂, h₄, h₃⟩ := exists_restrict_network N C (hM.image _) (hC.restrictRows C) hdisp
  have hle : RS .single (C.domRestrict N.ancestral) (restrictRows C M) ≤ N''.recombCount := Nat.sInf_le ⟨a, b, N'', h₁ _ (obeys_liftSites_single C hc), h₂, h₄, rfl⟩
  exact hle.trans h₃

/-- The same with multiple crossovers. -/
theorem RS_multiple_restrictRows_le_breakCount {E : Type w} [Finite E] [Finite ι] (N : Network ι V E) {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hd : ∀ r ∈ M, ∃ v, N.label v = r) (C : Set ι) : RS .multiple (C.domRestrict N.ancestral) (restrictRows C M) ≤ breakCount N C := by
  have hdisp : ∀ r ∈ restrictRows C M, ∃ v, C.domRestrict (N.label v) = r := fun r hr => by
    obtain ⟨ρ, hρ, rfl⟩ := mem_restrictRows.1 hr
    obtain ⟨v, rfl⟩ := hd ρ hρ
    exact ⟨v, rfl⟩
  obtain ⟨a, b, N'', h₁, h₂, h₄, h₃⟩ := exists_restrict_network N C (hM.image _) (hC.restrictRows C) hdisp
  have hle : RS .multiple (C.domRestrict N.ancestral) (restrictRows C M) ≤ N''.recombCount := Nat.sInf_le ⟨a, b, N'', h₁ _ trivial, h₂, h₄, rfl⟩
  exact hle.trans h₃

end Reduce

/-! ### The events of a network satisfy the system -/

section Events

variable {S : ℕ} {V : Type v} {E : Type w}

/-- A lower set of sites is an initial segment. So a single crossover is at one point. -/
theorem exists_cut (L : LowerSet (Fin S)) : ∃ c : ℕ, ∀ a : Fin S, a ∈ L ↔ a.val < c := by
  classical
  refine ⟨(Finset.univ.filter (· ∈ L)).sup fun a => a.val + 1, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · exact Nat.lt_of_succ_le (Finset.le_sup (f := fun a : Fin S => a.val + 1) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩))
  · by_contra hna
    have hle : (Finset.univ.filter (· ∈ L)).sup (fun a : Fin S => a.val + 1) ≤ a.val := by
      refine Finset.sup_le fun b hb => ?_
      have hbL : b ∈ L := (Finset.mem_filter.1 hb).2
      by_contra hc
      exact hna (L.lower (Fin.le_def.2 (by omega)) hbL)
    omega

/-- A recombination node breaks a region only if its crossover is in that region. -/
theorem exists_crossover (N : Network (Fin S) V E) (hc : N.Obeys .single) {x : V} (hx : N.IsRecomb x) :
    ∃ c : ℕ, ∀ i j, N.BreaksAt x (region S i j) → i < c ∧ c ≤ j := by
  rw [obeys_iff] at hc
  obtain ⟨e, f, -, he, hf, L, hL⟩ := hc x hx
  obtain ⟨c, hc⟩ := exists_cut L
  refine ⟨c, fun i j hb => ⟨?_, ?_⟩⟩
  · by_contra hi
    refine hb f hf (funext ?_)
    rintro ⟨a, ha₁, -⟩
    have hna : a ∉ L := fun h => by
      have := (hc a).1 h
      omega
    change N.label x a = N.label (N.src f) a
    rw [hL a, ite_eq_right hna]
  · by_contra hj
    refine hb e he (funext ?_)
    rintro ⟨a, -, ha₂⟩
    have ha : a ∈ L := (hc a).2 (by omega)
    change N.label x a = N.label (N.src e) a
    rw [hL a, ite_eq_left ha]

/-- **The events of a network satisfy the system** (`ext:mg_events`). Each recombination node has one crossover, in one of the intervals between consecutive sites, and `r_l` counts those in the interval `l`, so `Σ r_l` is at most the number of recombination nodes. A node breaking the region from `i` to `j` has its crossover in that region: `B_ij ≤ Σ_{l=i}^{j-1} r_l` when `B_ij` is at most the number of such nodes. -/
theorem exists_feasible [Finite V] (N : Network (Fin S) V E) (hc : N.Obeys .single) {B : ℕ → ℕ → ℕ}
    (hB : ∀ i j, i < j → j < S → B i j ≤ breakCount N (region S i j)) :
    ∃ r, Feasible S B r ∧ ∀ s t, ∑ l ∈ Finset.Ico s t, r l ≤ N.recombCount := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hcut : ∀ x : {x // N.IsRecomb x}, ∃ c : ℕ, ∀ i j, N.BreaksAt x.1 (region S i j) → i < c ∧ c ≤ j := fun x => exists_crossover N hc x.2
  choose c hcc using hcut
  set cut : V → ℕ := fun v => if h : N.IsRecomb v then c ⟨v, h⟩ - 1 else 0 with hcutdef
  set X : Finset V := Finset.univ.filter N.IsRecomb with hX
  have hXcard : N.recombCount = X.card := by
    unfold recombCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine ⟨fun l => (X.filter fun v => cut v = l).card, ?_, ?_⟩
  · intro i j hij hj
    refine (hB i j hij hj).trans ?_
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    unfold breakCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine Finset.card_le_card fun v hv => ?_
    obtain ⟨hv₁, hv₂⟩ := (Finset.mem_filter.1 hv).2
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hv₁⟩, ?_⟩
    obtain ⟨h₁, h₂⟩ := hcc ⟨v, hv₁⟩ i j hv₂
    have hcv : cut v = c ⟨v, hv₁⟩ - 1 := dite_eq_left hv₁
    rw [hcv, Finset.mem_Ico]
    omega
  · intro s t
    rw [Finset.sum_card_fiberwise_eq_card_filter, hXcard]
    exact Finset.card_filter_le _ _

/-- **The composite bound for a network** (`ext:mg_composite_network`). -/
theorem algorithm1_le_recombCount [Finite V] (N : Network (Fin S) V E) (hc : N.Obeys .single) {B : ℕ → ℕ → ℕ}
    (hB : ∀ i j, i < j → j < S → B i j ≤ breakCount N (region S i j)) {s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    algorithm1 B S s t ≤ N.recombCount := by
  obtain ⟨r, hr, htotal⟩ := exists_feasible N hc hB
  exact (algorithm1_le_sum B hst ht hr).trans (htotal s t)

/-- `B` is a family of local bounds for the rows `M`: "suppose we have some method of obtaining a local bound `B_ij` on the number of recombinations in the region `(s_i, s_j)`". Here the network need only have the rows among the labels of its nodes, so that an ancestral sequence can be one of them. -/
def IsLocalBounds (M : Finset (Fin S → Bool)) (B : ℕ → ℕ → ℕ) : Prop :=
  ∀ (a b : ℕ) (N : Network (Fin S) (Fin a) (Fin b)), N.Obeys .single → (∀ r ∈ M, ∃ v, N.label v = r) →
    ∀ i j, i < j → j < S → B i j ≤ breakCount N (region S i j)

theorem IsLocalBounds.mono {M : Finset (Fin S → Bool)} {B B' : ℕ → ℕ → ℕ} (h : IsLocalBounds M B') (hB : ∀ i j, i < j → j < S → B i j ≤ B' i j) : IsLocalBounds M B :=
  fun a b N hc hd i j hij hj => (hB i j hij hj).trans (h a b N hc hd i j hij hj)

/-- **The composite bound** (`ext:mg_composite`). The value of Algorithm 1 on local bounds is a lower bound on `R¹`. This holds for `R_st`, for any two sites. In particular `R_{1S} ≤ R¹(M)`. -/
theorem algorithm1_le_R {M : Finset (Fin S → Bool)} (hM : M.Nonempty) {B : ℕ → ℕ → ℕ} (hB : IsLocalBounds M B) {s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    algorithm1 B S s t ≤ R .single M := by
  obtain ⟨a, b, N, hc, hd, h⟩ := Nat.sInf_mem (recombSet_nonempty .single hM)
  have := algorithm1_le_recombCount N hc (hB a b N hc hd.displays) hst ht
  rw [h] at this
  exact this

/-- **The composite bound with known ancestral types** (`ext:mg_composite_rooted`): "the improved set of equations obtained when types are known corresponds to adding an all-zero type to the top of our list of sequences and then proceeding as if types were unknown". The local bounds are those of `M + S₀`. -/
theorem algorithm1_le_RS {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (S₀ : Fin S → Bool) {B : ℕ → ℕ → ℕ} (hB : IsLocalBounds (addRow M S₀) B) {s t : ℕ} (hst : s ≤ t) (ht : t < S) :
    algorithm1 B S s t ≤ RS .single S₀ M := by
  obtain ⟨a, b, N, hc, hd, hS, h⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .single S₀ hM)
  have hdisp : ∀ r ∈ addRow M S₀, ∃ v, N.label v = r := fun r hr => by
    rcases mem_addRow.1 hr with rfl | hr
    · exact ⟨N.root, hS⟩
    · exact hd.displays r hr
  have := algorithm1_le_recombCount N hc (hB a b N hc hdisp) hst ht
  rw [h] at this
  exact this

/-! ### The local bounds -/

/-- **`R¹` of the region is a local bound** (`ext:mg_local_region`). -/
theorem isLocalBounds_region {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M) :
    IsLocalBounds M fun i j => R .single (restrictRows (region S i j) M) :=
  fun _ _ N hc hd _ _ _ _ => R_restrictRows_le_breakCount N hc hM hC hd _

/-- **Two regions** (`ext:mg_two_regions_R`). Regions sharing at most an end point: `R¹(M(s..k)) + R¹(M(k..t)) ≤ R¹(M)`. Compare `Gusfield2007.Gen.split`, with any two sets of sites, the first to the left of the second, and `R` of multiple crossovers on them. -/
theorem add_R_le_R {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M) {s k t : ℕ} (hsk : s < k) (hkt : k < t) (ht : t < S) :
    R .single (restrictRows (region S s k) M) + R .single (restrictRows (region S k t) M) ≤ R .single M := by
  set B : ℕ → ℕ → ℕ := fun i j => R .single (restrictRows (region S i j) M)
  have h₁ := le_algorithm1 B hsk (hkt.trans ht)
  have h₂ := le_algorithm1 B hkt ht
  have h₃ := algorithm1_add_le B hsk.le hkt.le ht
  have h₄ := algorithm1_le_R hM (isLocalBounds_region (M := M) hM hC) (hsk.trans hkt).le ht
  exact (add_le_add h₁ h₂).trans (h₃.trans h₄)

/-- The four-gamete test, on the pair of ends of a region. -/
theorem isLocalBounds_fourGamete (M : Finset (Fin S → Bool)) :
    IsLocalBounds M (HudsonKaplan1985.incompatBounds (HudsonKaplan1985.fourGamete M)) := by
  intro a b N _ hd i j hij hj
  unfold HudsonKaplan1985.incompatBounds
  split_ifs with hdij
  · have hinc : Incompatible M ⟨i, hij.trans hj⟩ ⟨j, hj⟩ := (HudsonKaplan1985.fourGamete_eq_true_iff ⟨i, hij.trans hj⟩ ⟨j, hj⟩).1 hdij
    obtain ⟨x, hx, hb⟩ := N.exists_breaksAt_of_incompatible hd hinc
    have hsub : ({⟨i, hij.trans hj⟩, ⟨j, hj⟩} : Set (Fin S)) ⊆ region S i j := by
      rintro _ (rfl | rfl)
      · exact ⟨le_rfl, hij.le⟩
      · exact ⟨hij.le, le_rfl⟩
    have hpos : 0 < breakCount N (region S i j) := by
      unfold breakCount
      have : Nonempty {x // N.IsRecomb x ∧ N.BreaksAt x (region S i j)} := ⟨⟨x, hx, breaksAt_mono hb hsub⟩⟩
      exact Nat.card_pos
    exact hpos
  · exact Nat.zero_le _

/-- The haplotype bound: "each recombination or mutation event in the ancestry creates at most one new type", and the ancestor is at most one more. A recombination node that doesn't break the sites `T` creates no new type on them. -/
theorem typeCount_le {V E : Type*} [Finite V] (N : Network (Fin S) V E) {M : Finset (Fin S → Bool)} (hd : ∀ r ∈ M, ∃ v, N.label v = r) (T : Finset (Fin S)) :
    typeCount M T ≤ 1 + T.card + breakCount N (T : Set (Fin S)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  set mask : (Fin S → Bool) → Fin S → Bool := fun r a => decide (a ∈ T) && r a with hmask
  set X : Finset V := Finset.univ.filter fun x => N.IsRecomb x ∧ N.BreaksAt x (T : Set (Fin S)) with hX
  have hXcard : breakCount N (T : Set (Fin S)) = X.card := by
    unfold breakCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set U : Finset V := insert N.root (T.image fun i => N.tgt (N.site i) ) ∪ X with hU
  have hsub : M.image mask ⊆ U.image fun u => mask (N.label u) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨v, rfl⟩ := hd r hr
    obtain ⟨u, hu, hul⟩ := N.exists_source (T : Set (Fin S)) v
    refine Finset.mem_image.2 ⟨u, ?_, ?_⟩
    · rcases hu with rfl | ⟨i, hi, rfl⟩ | hu
      · simp [hU]
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hi)))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩)
    · funext a
      by_cases ha : a ∈ T
      · simp [hmask, ha, hul a (Finset.mem_coe.2 ha)]
      · simp [hmask, ha]
  calc typeCount M T = (M.image mask).card := rfl
    _ ≤ (U.image fun u => mask (N.label u)).card := Finset.card_le_card hsub
    _ ≤ U.card := Finset.card_image_le
    _ ≤ (insert N.root (T.image fun i => N.tgt (N.site i))).card + X.card := Finset.card_union_le _ _
    _ ≤ (T.image (fun i => N.tgt (N.site i))).card + 1 + X.card := by
      gcongr
      exact Finset.card_insert_le _ _
    _ ≤ T.card + 1 + X.card := by
      gcongr
      exact Finset.card_image_le
    _ = 1 + T.card + breakCount N (T : Set (Fin S)) := by
      rw [hXcard]
      ring

/-- **The haplotype bounds are local bounds** (`ext:mg_local_haplotype`): "there is no reason why we may not apply it to any subset of sites in the data", and it then "holds for the region between the endpoint sites in our set". -/
theorem isLocalBounds_haplotypeBounds (M : Finset (Fin S → Bool)) : IsLocalBounds M (haplotypeBounds M) := by
  intro a b N _ hd i j _ _
  refine Finset.sup_le fun T hT => ?_
  have hsub : (T : Set (Fin S)) ⊆ region S i j := fun c hc => (Finset.mem_filter.1 hT).2.2.2 c (Finset.mem_coe.1 hc)
  have h₁ := typeCount_le N hd T
  have h₂ := breakCount_mono N hsub
  unfold haplotypeAt
  omega

/-- "If we consider only the subsets consisting of pairs of elements (i.e., the endpoint pairs) the haplotype bound is equivalent to the three- or four-gamete test": a pair with all four gametes has four types, and `4 - 2 - 1 = 1`. -/
theorem incompatBounds_le_haplotypeBounds (M : Finset (Fin S → Bool)) {i j : ℕ} (hij : i < j) (hj : j < S) :
    HudsonKaplan1985.incompatBounds (HudsonKaplan1985.fourGamete M) i j ≤ haplotypeBounds M i j := by
  unfold HudsonKaplan1985.incompatBounds
  split_ifs with hdij
  · set a : Fin S := ⟨i, hij.trans hj⟩
    set b : Fin S := ⟨j, hj⟩
    have hab : a ≠ b := fun h => hij.ne (congrArg Fin.val h)
    have hinc : Incompatible M a b := (HudsonKaplan1985.fourGamete_eq_true_iff a b).1 hdij
    have hT : ({a, b} : Finset (Fin S)) ∈ (Finset.univ : Finset (Finset (Fin S))).filter (HasEndpoints i j) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨a, by simp, rfl⟩, ⟨b, by simp, rfl⟩, fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨le_rfl, hij.le⟩
      · rw [Finset.mem_singleton.1 hc]
        exact ⟨hij.le, le_rfl⟩
    refine le_trans ?_ (Finset.le_sup (f := haplotypeAt M) hT)
    unfold haplotypeAt
    rw [Finset.card_pair hab]
    have h4 : 4 ≤ typeCount M {a, b} := by
      have hsurj : (Finset.univ : Finset (Bool × Bool)) ⊆ (M.image fun r c => decide (c ∈ ({a, b} : Finset (Fin S))) && r c).image fun t => (t a, t b) := by
        rintro ⟨p, q⟩ -
        obtain ⟨r, hr, h₁, h₂⟩ := hinc p q
        refine Finset.mem_image.2 ⟨_, Finset.mem_image_of_mem _ hr, ?_⟩
        simp [h₁, h₂]
      have h := (Finset.card_le_card hsurj).trans Finset.card_image_le
      have h₄ : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
      rw [h₄] at h
      exact h
    omega
  · exact Nat.zero_le _

/-- **`R_m ≤ R_h`** (`ext:mg_rm_le_rh`), on a nonempty list of sites. -/
theorem Rm_le_Rh (M : Finset (Fin S → Bool)) (hS : 0 < S) : Rm M ≤ Rh M :=
  algorithm1_mono (fun _ _ hij hj => incompatBounds_le_haplotypeBounds M hij hj) (Nat.zero_le _) (by omega)

/-- **`R_h` is a lower bound on `R¹`** (`ext:mg_rh_le`): "this collection of local bounds gives the overall bound `R_h` when Algorithm 1 is applied". -/
theorem Rh_le_R {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hS : 0 < S) : Rh M ≤ R .single M :=
  algorithm1_le_R hM (isLocalBounds_haplotypeBounds M) (Nat.zero_le _) (by omega)

/-- **`R_m` is a lower bound on `R¹`** (`ext:mg_rm_le`), through the composite bound, and it's `R_M` of Hudson and Kaplan, whose own proof is `HudsonKaplan1985.rM_le_R`: "both methods lead to the same bound". -/
theorem Rm_eq_rM (M : Finset (Fin S → Bool)) (hS : 0 < S) : Rm M = HudsonKaplan1985.rM M :=
  (HudsonKaplan1985.hudsonKaplan_eq_algorithm1 hS).symm

theorem Rm_le_R {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (hS : 0 < S) : Rm M ≤ R .single M :=
  algorithm1_le_R hM (isLocalBounds_fourGamete M) (Nat.zero_le _) (by omega)

/-- **`R_m`, `R_h` with known ancestral types** (`ext:mg_rh_rooted`): "if we always add an all-zero type (before any other analysis) to the front of the list of types in this case, as before it is clear that applying the type's unknown bound will always give the correct lower bound here". -/
theorem Rh_addRow_le_RS {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (S₀ : Fin S → Bool) (hS : 0 < S) : Rh (addRow M S₀) ≤ RS .single S₀ M :=
  algorithm1_le_RS hM S₀ (isLocalBounds_haplotypeBounds _) (Nat.zero_le _) (by omega)

theorem Rm_addRow_le_RS {M : Finset (Fin S → Bool)} (hM : M.Nonempty) (S₀ : Fin S → Bool) (hS : 0 < S) : Rm (addRow M S₀) ≤ RS .single S₀ M :=
  algorithm1_le_RS hM S₀ (isLocalBounds_fourGamete _) (Nat.zero_le _) (by omega)

end Events

end MyersGriffiths2003
