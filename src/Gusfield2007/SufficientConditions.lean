module

public import Gusfield2007.Conjectures
public import Gusfield2007.NetworkOps
public import Gusfield2007.Parsimony
public import External.MyersGriffiths2003.Bound

/-!
# Gusfield et al. 2007, Section 5.2: sufficient conditions for `M` to be S-min or S-min-1 decomposable

Lemma 5, Theorem 7, Corollary 3, Theorem 8, Theorem 9, Theorem 5, Corollary 2, Theorem 10, Theorem 6, in the order of their
proofs. A statement with a crossover model `c` covers the two cases of the paper (`c = multiple`, `c = single`), and the model of
back and recurrent mutation that Corollary 3 needs.

The proofs follow the paper. Where it says "the resulting network derives", Lean has to trim the network, because `Derives` has the rows exactly at the leaves: `Network.exists_derives_of_displays`. The statements that aren't in the paper as printed are at
`theorem10`, `theorem10_multiple` and `visibleOfTightPrinted_false`. Two more sentences of the paper are here: `unrootedParsimonyScore_eq_sum` (line 411) and `sum_le_RS_of_sMinDecomposable` (line 420).
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E]

/-- **Theorem 7** (`g:thm7`). "Let `N` be a phylogenetic network for `M` with ancestral sequence `S` such that every recombination node in `N` is
either a 0 or 1-component recombination node, relative to `G_S(M)`. Then there is fully-decomposed phylogenetic network `N'` for `M`, with ancestral
sequence `S`, using at most `R(N)` recombination nodes, where both `N` and `N'` allow the same type of recombinations" (line 492). -/
theorem theorem7 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄, h₅⟩ := theorem3 c M S hd.nonempty hC
  exact ⟨a, b, N', h₁, h₂, h₃, h₄, h₅.trans_le (lemma5 hC N hc hd hS h)⟩

/-- An optimal network whose recombination nodes are 0 or 1-component shows that `M` is S-min decomposable, by Theorem 7: the fully-decomposed network has no more recombination nodes, and so as many. -/
theorem sMinDecomposable_of_isOptimalRooted {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hN : N.IsOptimalRooted c S M)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) : SMinDecomposable c S M := by
  obtain ⟨hc, hd, hS, hcount⟩ := hN
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄, h₅⟩ := theorem7 hC N hc hd hS h
  exact ⟨a, b, N', h₁, h₂, h₃, h₄, le_antisymm (h₅.trans hcount.le) (RS_le_recombCount N' h₁ h₂ h₃)⟩

omit [Fintype V] [Finite E] in
/-- A tree exists for any ancestral sequence, from a network of recombinations modelling mutations (Theorem 1 with an ancestral sequence). -/
theorem exists_mutationTree_of_nonempty (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) :
    ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), T.label T.root = S ∧ Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧
      T.mutationCount ≤ Nat.card ι + RS .pointwise S M := by
  obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .pointwise S hM)
  change N.recombCount = RS .pointwise S M at hcount
  obtain ⟨E', _, T, h₁, h₂, h₃⟩ := N.exists_mutationTree hc
  obtain ⟨a', b', T', h₁', h₂', h₃'⟩ := MutationTree.exists_fin_of_displays T (M := M) hM fun r hr => by
    rw [h₂]
    exact hd.displays r hr
  refine ⟨a', b', T', ?_, h₂', h₃'.trans (h₃.trans (by rw [hcount]))⟩
  rw [h₁', h₁, h₂]
  exact hS

/-- **Bridge for Corollary 3** (`g:parsimony_bridge`). Each mutation beyond the first at a site is one recombination modelling it (lines 358, 511):
the parsimony score with ancestral sequence `S` is the number of sites plus `R_S(M)` in the model of back and recurrent mutation. The
standing assumption is needed: a constant column at the state of `S` costs no mutation, but it must mutate on a network. -/
theorem parsimonyScore_eq (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    parsimonyScore S M = Nat.card ι + RS .pointwise S M := by
  have hne : {k | ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), T.label T.root = S ∧
      Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧ T.mutationCount = k}.Nonempty := by
    obtain ⟨a, b, T, h₁, h₂, -⟩ := exists_mutationTree_of_nonempty M S hM
    exact ⟨_, a, b, T, h₁, h₂, rfl⟩
  apply le_antisymm
  · obtain ⟨a, b, T, h₁, h₂, h₃⟩ := exists_mutationTree_of_nonempty M S hM
    have h : parsimonyScore S M ≤ T.mutationCount := Nat.sInf_le ⟨a, b, T, h₁, h₂, rfl⟩
    exact h.trans h₃
  · obtain ⟨a, b, T, h₁, h₂, h₃⟩ := Nat.sInf_mem hne
    have : Fintype ι := Fintype.ofFinite ι
    have := T.card_add_RS_le hM hC fun r hr => by
      obtain ⟨v, -, hv⟩ := h₂.surjOn hr
      exact ⟨v, hv⟩
    rw [h₁, h₃] at this
    rw [Nat.card_eq_fintype_card]
    exact this

omit [Fintype V] [Finite E] [Finite ι] in
/-- A recombination that models a mutation is a 0 or 1-component recombination (line 511): for every component not containing the site, "the recombinant sequence is identical to one of its parent sequences at the sites". -/
theorem isZero_or_isOne_of_pointwise {G : SimpleGraph ι} (N : Network ι V E) (hc : N.Obeys .pointwise) (x : V) (hx : N.IsRecomb x) :
    N.IsZeroComponent G x ∨ N.IsOneComponent G x := by
  by_cases hz : N.IsZeroComponent G x
  · exact Or.inl hz
  · right
    unfold Network.IsZeroComponent at hz
    push Not at hz
    obtain ⟨C, hC⟩ := hz
    obtain ⟨e, f, -, he, -, j, hj⟩ := hc x hx
    have hmem : ∀ C₁ : G.ConnectedComponent, N.BreaksAt x C₁.supp → j ∈ C₁.supp := by
      intro C₁ hb
      by_contra hno
      refine hb e he (funext fun i => ?_)
      have hij : i.1 ≠ j := fun h => hno (h ▸ i.2)
      have := hj i.1
      rwa [ite_eq_right hij] at this
    exact ⟨C, hC, fun C' hb => SimpleGraph.ConnectedComponent.eq_of_common_vertex (hmem C' hb) (hmem C hC)⟩

omit [Fintype V] [Finite E] in
/-- `R_S(M)` splits over the components, in the model of recombinations that model mutations. -/
theorem RS_pointwise_eq_sum (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    RS .pointwise S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS .pointwise (C.supp.domRestrict S) (restrictRows C.supp M) := by
  apply le_antisymm
  · obtain ⟨a, b, N, h₁, h₂, h₃, -, h₅⟩ := theorem3 .pointwise M S hM hC
    exact (RS_le_recombCount N h₁ h₂ h₃).trans h₅.le
  · obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .pointwise S hM)
    exact (lemma5 hC N hc hd hS fun x hx => isZero_or_isOne_of_pointwise N hc x hx).trans hcount.le

omit [Fintype V] [Finite E] in
/-- **Corollary 3** (`g:cor3`). "When recombinations only model back or recurrent mutations (as detailed in Section 4.1), then `M` is S-min
decomposable for any sequence `S`, and the maximum parsimony problem for `M` can be solved by separately solving a maximum parsimony problem for
the sites from each connected component of `G_S(M)`" (line 506).

"S-min decomposable" is in the model of those recombinations: it can't be for `multiple`, by `g:multiple_false`. -/
theorem corollary3 (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    SMinDecomposable .pointwise S M ∧
      parsimonyScore S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) := by
  constructor
  · obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .pointwise S hM)
    exact sMinDecomposable_of_isOptimalRooted hC N ⟨hc, hd, hS, hcount⟩ fun x hx => isZero_or_isOne_of_pointwise N hc x hx
  · have : Finite (conflictGraph S M).ConnectedComponent := Finite.of_surjective _ Quot.mk_surjective
    have : Fintype (conflictGraph S M).ConnectedComponent := Fintype.ofFinite _
    have hcomp : ∀ C : (conflictGraph S M).ConnectedComponent, parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) =
        Nat.card C.supp + RS .pointwise (C.supp.domRestrict S) (restrictRows C.supp M) := fun C => by
      refine parsimonyScore_eq _ _ ?_ (hC.restrictRows C.supp)
      obtain ⟨r, hr⟩ := hM
      exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
    have hcard : ∑ C : (conflictGraph S M).ConnectedComponent, Nat.card C.supp = Nat.card ι := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (Equiv.sigmaFiberEquiv (conflictGraph S M).connectedComponentMk)
    rw [parsimonyScore_eq M S hM hC, RS_pointwise_eq_sum M S hM hC, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun C _ => hcomp C, Finset.sum_add_distrib, hcard]

/-- The maximum parsimony score of `M` with no ancestral sequence specified (line 411). -/
noncomputable def unrootedParsimonyScore (M : Finset (ι → Bool)) : ℕ :=
  sInf {k | ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧ T.mutationCount = k}

omit [Fintype V] [Finite E] in
/-- With no ancestral sequence specified, any row of `M` is an optimal one, by re-rooting. -/
theorem unrootedParsimonyScore_eq_of_mem {M : Finset (ι → Bool)} {r : ι → Bool} (hr : r ∈ M) : unrootedParsimonyScore M = parsimonyScore r M := by
  have hM : M.Nonempty := ⟨r, hr⟩
  have hnonempty : ∀ S : ι → Bool, {k | ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), T.label T.root = S ∧
      Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧ T.mutationCount = k}.Nonempty := fun S => by
    obtain ⟨a, b, T, h₁, h₂, -⟩ := exists_mutationTree_of_nonempty M S hM
    exact ⟨_, a, b, T, h₁, h₂, rfl⟩
  apply le_antisymm
  · obtain ⟨a, b, T, -, h₂, h₃⟩ := Nat.sInf_mem (hnonempty r)
    exact Nat.sInf_le ⟨a, b, T, h₂, h₃⟩
  · have hne : {k | ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧ T.mutationCount = k}.Nonempty := by
      obtain ⟨a, b, T, -, h₂, h₃⟩ := Nat.sInf_mem (hnonempty r)
      exact ⟨_, a, b, T, h₂, h₃⟩
    obtain ⟨a, b, T, h₂, h₃⟩ := Nat.sInf_mem hne
    have h₁ : parsimonyScore (T.label T.root) M ≤ T.mutationCount := Nat.sInf_le ⟨a, b, T, rfl, h₂, rfl⟩
    exact (MutationTree.parsimonyScore_row_le hr (hnonempty _)).trans (h₁.trans h₃.le)

omit [Fintype V] [Finite E] in
/-- **Line 411** (`g:mutation_min`). "When the recombination events only model recurrent and back mutations, then every `M` is min decomposable."

Departure from the paper, not forced: it proves a specialization, Corollary 3, and says that the general statement "follows from results on the maximum parsimony problem using median networks, as established by Bandelt et al. (1995)". Those results are there: all most parsimonious trees can be realized in the median network (p. 745), and at a cut node of that network the characters split into two sets, and the most parsimonious trees "are exactly the trees composed by the MP trees" of the two parts (p. 747; "decomposition along cut nodes", p. 748). Neither paper writes the link from cut nodes to the components of `G(M)`, which the statement needs.
Lean derives it from Corollary 3 instead: the parsimony score doesn't change on re-rooting at a row of an optimal tree (`MutationTree.parsimonyScore_row_le`), so an optimal `S` can be taken in `M`, where `G_S(M) = G(M)`, and Corollary 3 applies at that `S`. The route by cut nodes wasn't built, for its cost: it needs the median network, its retract property, which Bandelt et al. cite (Bandelt 1984, van de Vel 1993) and don't prove, and that link. -/
theorem minDecomposable_pointwise (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    MinDecomposable .pointwise M := by
  obtain ⟨r, hr⟩ := hM
  have hM : M.Nonempty := ⟨r, hr⟩
  obtain ⟨a, b, N, hc, hd, hcount⟩ := Nat.sInf_mem (recombSet_nonempty .pointwise hM)
  change N.recombCount = R .pointwise M at hcount
  have hle : RS .pointwise N.ancestral M ≤ R .pointwise M := hcount ▸ RS_le_recombCount N hc hd rfl
  have hscore : parsimonyScore r M ≤ parsimonyScore N.ancestral M := by
    obtain ⟨a', b', T, h₁, h₂, -⟩ := exists_mutationTree_of_nonempty M N.ancestral hM
    exact MutationTree.parsimonyScore_row_le hr ⟨_, a', b', T, h₁, h₂, rfl⟩
  rw [parsimonyScore_eq M r hM hC, parsimonyScore_eq M _ hM hC] at hscore
  have hRS : RS .pointwise r M = R .pointwise M := le_antisymm (by omega) (R_le_RS .pointwise r hM)
  obtain ⟨a', b', N', h₁, h₂, -, h₄, h₅⟩ := (corollary3 M r hM hC).1
  rw [conflictGraph_eq_of_mem hr] at h₄
  exact ⟨a', b', N', h₁, h₂, h₄, h₅.trans hRS⟩

omit [Fintype V] [Finite E] in
/-- **Line 411, second sentence** (`g:mutation_split`). "When incompatibilities are caused by recurrent and/or back mutation, one can solve the maximum parsimony problem exactly for each set `M(C)` separately, and then connect the trees as specified by `T̄`": with no ancestral sequence
specified, the parsimony score of `M` is the sum over the components of `G(M)`. A row of `M` is an optimal ancestral sequence, and its restrictions are optimal for `M(C)`, so Corollary 3 applies at that row. -/
theorem unrootedParsimonyScore_eq_sum (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    unrootedParsimonyScore M = ∑ᶠ C : (incompatGraph M).ConnectedComponent, unrootedParsimonyScore (restrictRows C.supp M) := by
  obtain ⟨r, hr⟩ := hM
  have h := (corollary3 M r ⟨r, hr⟩ hC).2
  rw [conflictGraph_eq_of_mem hr] at h
  rw [unrootedParsimonyScore_eq_of_mem hr, h]
  refine finsum_congr fun C => ?_
  rw [unrootedParsimonyScore_eq_of_mem (mem_restrictRows.2 ⟨r, hr, rfl⟩)]

omit [Fintype V] [Finite E] in
/-- **Line 420, rooted** (`g:lower_bound_sum_rooted`). "When the appropriate conjecture holds for an input `M`, we can also compute lower bounds on `R_S(M)`, `R¹_S(M)` by computing bounds separately for each `M(C)`, adding these bounds together for a valid overall lower bound. This is correct no matter what lower bound method is used." -/
theorem sum_le_RS_of_sMinDecomposable {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : SMinDecomposable c S M) (b : (conflictGraph S M).ConnectedComponent → ℕ)
    (hb : ∀ C, b C ≤ RS c (C.supp.domRestrict S) (restrictRows C.supp M)) : ∑ᶠ C, b C ≤ RS c S M := by
  have : Finite (conflictGraph S M).ConnectedComponent := Finite.of_surjective _ Quot.mk_surjective
  have : Fintype (conflictGraph S M).ConnectedComponent := Fintype.ofFinite _
  rw [(sMinDecomposable_iff c M S hM hC).1 h, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact Finset.sum_le_sum fun C _ => hb C

/-- **Theorem 8** (`g:thm8`). "Given `S`, if `M` is spatially disjoint, then `M` is S-min-1 decomposable" (line 519).

A misprint in the proof, at line 525: "using `R¹(M + S)` single-crossover recombinations" should be `R¹_S(M)`, since the network is for `M` with
ancestral sequence `S`, and the two can differ. -/
theorem theorem8 {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : SpatiallyDisjoint S M) : SMinDecomposable .single S M := by
  obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .single S hM)
  refine sMinDecomposable_of_isOptimalRooted hC N ⟨hc, hd, hS, hcount⟩ fun x hx => ?_
  by_cases hz : N.IsZeroComponent (conflictGraph S M) x
  · exact Or.inl hz
  · right
    unfold Network.IsZeroComponent at hz
    push Not at hz
    obtain ⟨C, hC'⟩ := hz
    refine ⟨C, hC', fun C' hb => ?_⟩
    by_contra hne
    obtain ⟨e, f, -, he, hf, L, hL⟩ := hc x hx
    have hsplit : ∀ C₁ : (conflictGraph S M).ConnectedComponent, N.BreaksAt x C₁.supp →
        (∃ i ∈ C₁.supp, i ∈ L) ∧ ∃ i ∈ C₁.supp, i ∉ L := by
      intro C₁ hb₁
      constructor
      · by_contra hno
        push Not at hno
        refine hb₁ f hf (funext fun i => ?_)
        have := hL i.1
        rwa [ite_eq_right (hno i.1 i.2)] at this
      · by_contra hno
        push Not at hno
        refine hb₁ e he (funext fun i => ?_)
        have := hL i.1
        rwa [ite_eq_left (hno i.1 i.2)] at this
    obtain ⟨⟨u, hu, huL⟩, w, hw, hwL⟩ := hsplit C hC'
    obtain ⟨⟨u', hu', huL'⟩, w', hw', hwL'⟩ := hsplit C' hb
    have hlt : ∀ {p q : ι}, p ∈ L → q ∉ L → p < q := fun hp hq => not_le.1 fun hle => hq (L.lower hle hp)
    have h₁ : max u u' ∈ C.supp := (h C).out hu hw ⟨le_max_left _ _, max_le (hlt huL hwL).le (hlt huL' hwL).le⟩
    have h₂ : max u u' ∈ C'.supp := (h C').out hu' hw' ⟨le_max_right _ _, max_le (hlt huL hwL').le (hlt huL' hwL').le⟩
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex h₂ h₁)

omit [LinearOrder ι] [Finite ι] [Finite E] in
/-- `M + S ⊆ L` (lines 427, 533). -/
theorem addRow_subset_labelSet (N : Network ι V E) {M : Finset (ι → Bool)} {S : ι → Bool} (hd : N.Derives M) (hS : N.ancestral = S) :
    addRow M S ⊆ N.labelSet := by
  intro r hr
  rcases mem_addRow.1 hr with rfl | hr
  · exact Finset.mem_image.2 ⟨N.root, Finset.mem_univ _, hS⟩
  · obtain ⟨v, rfl⟩ := hd.displays r hr
    exact Finset.mem_image_of_mem _ (Finset.mem_univ v)

omit [LinearOrder ι] in
/-- **Line 533** (`g:respects_iff`). "Since `M + S ⊆ L`, any incompatible pair in `M + S` is incompatible in `L`, so `L` respects `G_S(M)` if and only if
`G_S(L)` and `G_S(M)` have the same number of components". -/
theorem respects_iff_card {L M : Finset (ι → Bool)} {S : ι → Bool} (h : addRow M S ⊆ L) :
    Respects L S M ↔
      Nat.card (conflictGraph S L).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent := by
  have hS : S ∈ L := h (mem_addRow.2 (Or.inl rfl))
  have hle : conflictGraph S M ≤ conflictGraph S L := by
    rw [conflictGraph_eq_incompatGraph_addRow, conflictGraph_eq_of_mem hS]
    exact fun i j hij a b => by
      obtain ⟨r, hr, h'⟩ := hij a b
      exact ⟨r, h hr, h'⟩
  have hadj : ∀ i j, (conflictGraph S L).Adj i j ↔ Incompatible L i j := fun i j => by
    rw [conflictGraph_eq_of_mem hS]
    exact Iff.rfl
  set φ : (conflictGraph S M).ConnectedComponent → (conflictGraph S L).ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hle) with hφ
  have hφmk : ∀ i, φ ((conflictGraph S M).connectedComponentMk i) = (conflictGraph S L).connectedComponentMk i := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨i, rfl⟩ := c.exists_rep
    exact ⟨_, hφmk i⟩
  have : Finite (conflictGraph S M).ConnectedComponent := Finite.of_surjective _ Quot.mk_surjective
  have : Finite (conflictGraph S L).ConnectedComponent := Finite.of_surjective _ Quot.mk_surjective
  constructor
  · intro hR
    have hinj : Function.Injective φ := by
      intro c c' hcc
      obtain ⟨i, rfl⟩ := c.exists_rep
      obtain ⟨j, rfl⟩ := c'.exists_rep
      have hreach : (conflictGraph S L).Reachable i j := SimpleGraph.ConnectedComponent.exact hcc
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      apply SimpleGraph.ConnectedComponent.sound
      clear hcc
      induction hreach with
      | refl => exact SimpleGraph.Reachable.refl _
      | tail _ hbc ih => exact ih.trans (hR _ _ ((hadj _ _).1 hbc))
    exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm
  · intro hcard i j hinc
    have hbij := hsurj.bijective_of_nat_card_le hcard.ge
    apply SimpleGraph.ConnectedComponent.exact
    apply hbij.1
    rw [hφmk, hφmk]
    exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable ((hadj i j).2 hinc))

omit [LinearOrder ι] [Finite ι] [Fintype V] [Finite E] in
/-- A trivial component isn't broken (line 550): at its one site, the recombinant has the state of a parent. -/
theorem not_breaksAt_of_subsingleton (N : Network ι V E) {x : V} (hx : N.IsRecomb x) {C : Set ι} (hC : C.Subsingleton) :
    ¬ N.BreaksAt x C := by
  obtain ⟨e, f, hef, he, hf⟩ := hx
  intro hb
  rcases C.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · exact hb e he (funext fun j => absurd j.2 (Set.notMem_empty _))
  · rcases N.label_recomb e f hef (he.trans hf.symm) i with h | h
    · refine hb e he (funext fun j => ?_)
      have hj : j.1 = i := hC j.2 hi
      change N.label x j.1 = N.label (N.src e) j.1
      rw [hj, ← he]
      exact h
    · refine hb f hf (funext fun j => ?_)
      have hj : j.1 = i := hC j.2 hi
      change N.label x j.1 = N.label (N.src f) j.1
      rw [hj, ← he]
      exact h

omit [LinearOrder ι] [Finite ι] [Fintype V] [Finite E] in
/-- The two cases of the proof of Theorem 9 (line 552): `h(C) = d_C`. If a parent has `d_C` on `C`, then `C` isn't broken; otherwise, by Corollary 1, both parents have `d_{C'}` on `C'`, and so `h` has, "no matter where
any crossovers occur", and `C'` isn't broken. -/
theorem breaksAt_aux (N : Network ι V E) {L : Finset (ι → Bool)} (hL : ∀ v, N.label v ∈ L) {x : V} (hx : N.IsRecomb x) {C C' : Set ι} {d : C → Bool} {d' : C' → Bool}
    (hcor : ∀ r ∈ L, (∀ i : C, r i = d i) ∨ ∀ i : C', r i = d' i) (hb : N.BreaksAt x C) (hb' : N.BreaksAt x C')
    (hd : ∀ i : C, N.label x i = d i) : False := by
  obtain ⟨e, f, hef, he, hf⟩ := hx
  have hne : ∀ g, N.tgt g = x → ∀ i : C', N.label (N.src g) i = d' i := by
    intro g hg
    rcases hcor _ (hL (N.src g)) with h | h
    · exact absurd (funext fun i : C => (hd i).trans (h i).symm) (hb g hg)
    · exact h
  refine hb' e he (funext fun i : C' => ?_)
  have h₁ := N.label_recomb e f hef (he.trans hf.symm) i
  rw [he] at h₁
  rcases h₁ with h₁ | h₁
  · exact h₁
  · exact h₁.trans ((hne f hf i).trans (hne e he i).symm)

omit [LinearOrder ι] [Finite ι] [Fintype V] [Finite E] in
/-- **The proof of Theorem 9** (lines 548 to 552), for `M₀ = M + S`, whose incompatibility graph is `G_S(M)`. If `L` respects its components, no recombination with labels in `L` breaks two of them. A misprint at line 552: the dominant sequences are in
`(M + S)(C)` and `(M + S)(C')`, not in `M(C)` and `M(C')`. The components are those of `G_S(M) = G(M + S)`, so Lemma 2 and Corollary 1 apply to `M + S`, and a dominant sequence can occur in `S(C)` only. -/
theorem not_breaksAt_of_respects (N : Network ι V E) {M₀ L : Finset (ι → Bool)} (hsub : M₀ ⊆ L)
    (hnew : ∀ i j, Incompatible L i j → (incompatGraph M₀).Reachable i j) (hL : ∀ v, N.label v ∈ L) {x : V} (hx : N.IsRecomb x)
    {c c' : (incompatGraph M₀).ConnectedComponent} (hne : c ≠ c') (hb : N.BreaksAt x c.supp) (hb' : N.BreaksAt x c'.supp) : False := by
  have hnt : c.supp.Nontrivial := by
    by_contra h
    exact not_breaksAt_of_subsingleton N hx (Set.not_nontrivial_iff.1 h) hb
  have hnt' : c'.supp.Nontrivial := by
    by_contra h
    exact not_breaksAt_of_subsingleton N hx (Set.not_nontrivial_iff.1 h) hb'
  obtain ⟨d, d', hdom⟩ := exists_isDominantFor M₀ hne
  have hdomL := lemma2 hsub hnew hne hnt hnt' hdom
  -- The components of `G(L)` are those of `G(M₀)`, so that Corollary 1 applies to `L`.
  have hreach : ∀ i j, (incompatGraph L).Reachable i j ↔ (incompatGraph M₀).Reachable i j := by
    intro i j
    constructor
    · intro h
      rw [SimpleGraph.reachable_iff_reflTransGen] at h
      induction h with
      | refl => exact SimpleGraph.Reachable.refl _
      | tail _ hbc ih => exact ih.trans (hnew _ _ hbc)
    · refine SimpleGraph.Reachable.mono fun i j hij a b => ?_
      obtain ⟨r, hr, h'⟩ := hij a b
      exact ⟨r, hsub hr, h'⟩
  obtain ⟨i₀, hi₀⟩ := c.nonempty_supp
  obtain ⟨i₀', hi₀'⟩ := c'.nonempty_supp
  have hsupp : ∀ {c₁ : (incompatGraph M₀).ConnectedComponent} {i₁ : ι}, i₁ ∈ c₁.supp →
      ∀ i, i ∈ ((incompatGraph L).connectedComponentMk i₁).supp ↔ i ∈ c₁.supp := by
    intro c₁ i₁ hi₁ i
    have hc₁ : (incompatGraph M₀).connectedComponentMk i₁ = c₁ := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hi₁
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, hreach,
      ← SimpleGraph.ConnectedComponent.eq, hc₁]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).symm
  have hneL : (incompatGraph L).connectedComponentMk i₀ ≠ (incompatGraph L).connectedComponentMk i₀' := by
    intro h
    have : i₀ ∈ ((incompatGraph L).connectedComponentMk i₀').supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact h
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hi₀ ((hsupp hi₀' _).1 this))
  have hdomL' : IsDominantFor L ((incompatGraph L).connectedComponentMk i₀).supp ((incompatGraph L).connectedComponentMk i₀').supp
      (fun i => d ⟨i.1, (hsupp hi₀ _).1 i.2⟩) (fun i => d' ⟨i.1, (hsupp hi₀' _).1 i.2⟩) := fun i i' =>
    hdomL ⟨i.1, (hsupp hi₀ _).1 i.2⟩ ⟨i'.1, (hsupp hi₀' _).1 i'.2⟩
  have hcor : ∀ r ∈ L, (∀ i : c.supp, r i = d i) ∨ ∀ i : c'.supp, r i = d' i := by
    intro r hr
    rcases corollary1 L hneL hdomL' hr with h | h
    · exact Or.inl fun i => congrFun h ⟨i.1, (hsupp hi₀ _).2 i.2⟩
    · exact Or.inr fun i => congrFun h ⟨i.1, (hsupp hi₀' _).2 i.2⟩
  rcases hcor _ (hL x) with h | h
  · exact breaksAt_aux N hL hx hcor hb hb' h
  · exact breaksAt_aux N hL hx (fun r hr => (hcor r hr).symm) hb' hb h

/-- **Theorem 9** (`g:thm9`). "Let `N` be a phylogenetic network for `M` with ancestral sequence `S`, and suppose that `L` respects `G_S(M)`. Then there is
fully-decomposed phylogenetic network `N'` for `M`, with ancestral sequence `S`, using at most `R(N)` recombination nodes, where `N` and `N'` allow the
same type of recombinations" (line 538). -/
theorem theorem9 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S) (h : Respects N.labelSet S M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount := by
  have hG := conflictGraph_eq_incompatGraph_addRow S M
  refine theorem7 hC N hc hd hS fun x hx => ?_
  rw [hG]
  by_cases hz : N.IsZeroComponent (incompatGraph (addRow M S)) x
  · exact Or.inl hz
  · right
    unfold Network.IsZeroComponent at hz
    push Not at hz
    obtain ⟨C, hC'⟩ := hz
    refine ⟨C, hC', fun C' hb => ?_⟩
    by_contra hne
    have hsub : addRow M S ⊆ N.labelSet := addRow_subset_labelSet N hd hS
    refine not_breaksAt_of_respects N hsub (fun i j hinc => ?_) (fun v => Finset.mem_image_of_mem _ (Finset.mem_univ v)) hx hne hb hC'
    rw [← hG]
    exact h i j hinc

/-- **Theorem 5** (`g:thm5`). "Let `N` be an optimal phylogenetic network for `M` with ancestral sequence `S`, allowing multiple-crossover recombination
(respectively allowing only single-crossover recombination), using `R_S(M)` (respectively `R¹_S(M)`) recombination nodes. Let `G_S(L)` be the conflict graph
for sequences `L` with respect to `S`. Then `M` is S-min (respectively S-min-1) decomposable if `G_S(M)` and `G_S(L)` have the same number of connected
components" (line 432). -/
theorem theorem5 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hN : N.IsOptimalRooted c S M)
    (h : Nat.card (conflictGraph S N.labelSet).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent) :
    SMinDecomposable c S M := by
  obtain ⟨hc, hd, hS, hcount⟩ := hN
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄, h₅⟩ := theorem9 hC N hc hd hS ((respects_iff_card (addRow_subset_labelSet N hd hS)).2 h)
  exact ⟨a, b, N', h₁, h₂, h₃, h₄, le_antisymm (h₅.trans hcount.le) (RS_le_recombCount N' h₁ h₂ h₃)⟩

/-- **Corollary 2** (`g:cor2`). "Let `N` be an optimal phylogenetic network for `M` with ancestral sequence `S`, allowing multiple-crossover recombination
(respectively allowing only single-crossover recombination). Then `M` is S-min (respectively S-min-1) decomposable, if every node in `N` is visible"
(line 440). A visible node is one labelled by a row of `M`; in the rooted case that means `L = M + S` (line 427). -/
theorem corollary2 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hN : N.IsOptimalRooted c S M) (h : N.AllVisible M S) : SMinDecomposable c S M := by
  obtain ⟨hc, hd, hS, hcount⟩ := hN
  have hresp : Respects N.labelSet S M := by
    intro i j hinc
    refine SimpleGraph.Adj.reachable ((conflict_iff_incompatible_addRow S M i j).2 fun a b => ?_)
    obtain ⟨r, hr, h'⟩ := hinc a b
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨_, h v, h'⟩
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄, h₅⟩ := theorem9 hC N hc hd hS hresp
  exact ⟨a, b, N', h₁, h₂, h₃, h₄, le_antisymm (h₅.trans hcount.le) (RS_le_recombCount N' h₁ h₂ h₃)⟩

/-- The sentence of lines 560 to 563, as printed: "`H(M + S) = R(N) = R¹(M + S)` (or `R(M + S)`) only when every node in `N` is labeled by a sequence in `M + S`".
False: see below. -/
def VisibleOfTightPrinted (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) : Prop :=
  ∀ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.IsOptimalRooted c S M → (N.recombCount : ℤ) = haplotypeBound (addRow M S) →
    (N.recombCount = R c (addRow M S)) → N.AllVisible M S

/-- The network of the counterexample `g:visible_false`: the root `00`, an arc with the first site to `10`, an arc with the second site to the leaf `11`, and an arc to the leaf `00`. -/
def chainNet : Network (Fin 2) (Fin 4) (Fin 3) where
  src := fun e => if e = 1 then 1 else 0
  tgt := Fin.succ
  root := 0
  site := Fin.castSucc
  label := fun v i => decide (v = 2 ∨ (v = 1 ∧ i = 0))
  simple := by decide
  acyclic := Network.acyclic_of_rank (fun v : Fin 4 => v.val) (by decide)
  root_iff := by decide
  inDegree_le_two := by decide
  site_not_recomb := by decide
  label_tree := by
    intro e _ i
    fin_cases e <;> fin_cases i <;> simp
  label_recomb := by
    intro e f hef h
    exact absurd h (by revert e f; decide)

theorem chainNet_derives : chainNet.Derives twoEqualColumns := by
  have hleaf : ∀ v : Fin 4, chainNet.IsLeaf v ↔ v = 2 ∨ v = 3 := by
    intro v
    change (∀ e : Fin 3, (if e = 1 then (1 : Fin 4) else 0) ≠ v) ↔ v = 2 ∨ v = 3
    revert v
    decide
  have h₀ : chainNet.label 3 = ofBits [0, 0] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : chainNet.label 2 = ofBits [1, 1] := by
    funext i
    fin_cases i <;> rfl
  have hne : (ofBits [1, 1] : Fin 2 → Bool) ≠ ofBits [0, 0] := fun h => by
    have := congrFun h 0
    simp [ofBits] at this
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
  · rcases (hleaf v).1 hv with rfl | rfl
    · rw [h₁]
      simp [twoEqualColumns]
    · rw [h₀]
      simp [twoEqualColumns]
  · rcases (hleaf u).1 hu with rfl | rfl <;> rcases (hleaf v).1 hv with rfl | rfl
    · rfl
    · rw [h₁, h₀] at huv
      exact absurd huv hne
    · rw [h₁, h₀] at huv
      exact absurd huv.symm hne
    · rfl
  · have hr' : r = ofBits [0, 0] ∨ r = ofBits [1, 1] := by simpa [twoEqualColumns] using hr
    rcases hr' with rfl | rfl
    · exact ⟨3, (hleaf 3).2 (Or.inr rfl), h₀⟩
    · exact ⟨2, (hleaf 2).2 (Or.inl rfl), h₁⟩

theorem haplotypeBound_twoEqualColumns : haplotypeBound twoEqualColumns = 0 := by
  have hne : (ofBits [0, 0] : Fin 2 → Bool) ≠ ofBits [1, 1] := fun h => by
    have := congrFun h 0
    simp [ofBits] at this
  have hcard : twoEqualColumns.card = 2 := Finset.card_pair hne
  have hrow : ∀ r ∈ twoEqualColumns, r 0 = r 1 := by
    intro r hr
    have hr' : r = ofBits [0, 0] ∨ r = ofBits [1, 1] := by simpa [twoEqualColumns] using hr
    rcases hr' with rfl | rfl <;> rfl
  have hcols : distinctColumns twoEqualColumns = 1 := by
    have : (Set.range fun i : Fin 2 => fun r : twoEqualColumns => (r : Fin 2 → Bool) i) =
        {fun r : twoEqualColumns => (r : Fin 2 → Bool) 0} := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · rfl
        · exact Set.mem_singleton_iff.2 (funext fun r => (hrow r.1 r.2).symm)
      · rintro rfl
        exact ⟨0, rfl⟩
    rw [distinctColumns, this, Set.ncard_singleton]
  simp [haplotypeBound, hcard, hcols]

/-- **Counterexample to the sentence of lines 560 to 563** (`g:visible_false`). `M = {00, 11}`, `S = 00`. Take the path from the root through `10` to the leaf `11`,
with the leaf `00` at the root. There's no recombination, `H(M + S) = 2 - 1 - 1 = 0`, and the node `10` isn't visible. Two identical columns
needn't be on one arc. The proof of the bound gives only that the labels are visible on one site per distinct column. -/
theorem visibleOfTightPrinted_false : ¬ VisibleOfTightPrinted .single twoEqualColumns (fun _ => false) := by
  intro h
  have hinj : Function.Injective chainNet.tgt := Fin.succ_injective _
  have h0 : chainNet.recombCount = 0 := Network.recombCount_eq_zero_of_tgt_injective hinj
  have hc : chainNet.Obeys .single := Network.obeys_of_tgt_injective hinj _
  have hS : chainNet.ancestral = fun _ => false := by
    funext i
    fin_cases i <;> rfl
  have hmem : (fun _ => false : Fin 2 → Bool) ∈ twoEqualColumns := by
    have : (fun _ => false : Fin 2 → Bool) = ofBits [0, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [this]
    simp [twoEqualColumns]
  have hadd : addRow twoEqualColumns (fun _ => false) = twoEqualColumns := addRow_eq_of_mem hmem
  have hRS : RS .single (fun _ => false) twoEqualColumns = 0 :=
    Nat.le_zero.1 (Nat.sInf_le ⟨4, 3, chainNet, hc, chainNet_derives, hS, h0⟩)
  have hR : R .single twoEqualColumns = 0 :=
    Nat.le_zero.1 (Nat.sInf_le ⟨4, 3, chainNet, hc, chainNet_derives, h0⟩)
  have hvis := h 4 3 chainNet ⟨hc, chainNet_derives, hS, h0.trans hRS.symm⟩
    (by rw [hadd, haplotypeBound_twoEqualColumns, h0]; rfl) (by rw [hadd, hR, h0]) 1
  rw [hadd] at hvis
  have hr' : chainNet.label 1 = ofBits [0, 0] ∨ chainNet.label 1 = ofBits [1, 1] := by
    simpa [twoEqualColumns] using hvis
  rcases hr' with hr' | hr'
  · have := congrFun hr' 0
    simp [chainNet, ofBits] at this
  · have := congrFun hr' 1
    simp [chainNet, ofBits] at this

/-- **Theorem 10, the first part as printed** (`g:thm10_printed`). "For a set of sequences `M` and a specified ancestral sequence `S`, if `H(M + S) = R¹(M + S)` then `M` is
S-min-1 decomposable, and if `H(M + S) = R(M + S)` then `M` is S-min decomposable" (line 568).

As printed it's unproved here, and not refuted. `R(M + S)` is a notation slip for the rooted count `R_S(M)`, as at line 525: the proof reasons on an optimal network for `M` with ancestral sequence `S`, using `R_S(M)` nodes, and treats that number
as `R(M + S)`, the minimum over all ancestral sequences (lines 560 to 563). They can differ under the hypothesis: for `M + S = {0000, 0101, 1000, 1010, 1110, 1111}` and `S = 0101`, with multiple
crossovers, `H(M + S) = R(M + S) = 1` and `R_S(M) = 2`. If `R_S(M) > R(M + S)`, the tight network has another root, and the proof doesn't apply. That example has one component, so the conclusion holds.
A search for an example with two components where the conclusion fails found none, within these limits: rows of the form `(x, 0)` or `(0, y)`, `S` a row, no compatible sites, and small sizes, of which the larger were only sampled. Its programs aren't in this repository. The form with `R_S(M)` is `theorem10`, which is what the proof of Theorem 6 needs. -/
def Theorem10Printed (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) : Prop :=
  haplotypeBound (addRow M S) = R c (addRow M S) → SMinDecomposable c S M

/-- The proof of Theorem 10 at lines 560 to 564, when the columns of `M + S` are distinct: an optimal network with `H(M + S)` recombination nodes has every node visible (`allVisible_of_eq`), and Corollary 2 applies. -/
theorem sMinDecomposable_of_haplotype_tight {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hinj : Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := by
  obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty c S hM)
  have hN : N.IsOptimalRooted c S M := ⟨hc, hd, hS, hcount⟩
  exact corollary2 hC N hN (MyersGriffiths2003.allVisible_of_eq N hd hS hinj (by rw [h, hcount]; rfl))

/-- **Theorem 10, multiple crossovers, without distinct columns** (`g:thm10_multiple`). If `H(M + S) = R_S(M)` then `M` is S-min decomposable. Line 560 is false when `M + S` has identical columns (`g:visible_false`), so the proof of the paper doesn't apply as it stands. So the route is this: restrict to one site for each class of identical columns of `M + S`, where the columns are distinct and `H` has the same value; `allVisible_of_eq` and Corollary 2 apply there; then put each duplicate on the arc of its representative, which keeps the blobs, the
number of recombination nodes and the crossover model, which is unconstrained. -/
theorem theorem10_multiple {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound (addRow M S) = RS .multiple S M) : SMinDecomposable .multiple S M := by
  set col : ι → addRow M S → Bool := fun i r => (r : ι → Bool) i with hcol
  set rep : ι → ι := fun i => Set.rangeSplitting col ⟨col i, i, rfl⟩ with hrep
  have hcol_rep : ∀ i, col (rep i) = col i := fun i => Set.apply_rangeSplitting col ⟨col i, i, rfl⟩
  have hrep_rep : ∀ i, rep (rep i) = rep i := fun i => congrArg (Set.rangeSplitting col) (Subtype.ext (hcol_rep i))
  have hrep_eq : ∀ {i j}, col i = col j → rep i = rep j := fun {i j} hij =>
    congrArg (Set.rangeSplitting col) (Subtype.ext hij)
  have hval : ∀ r ∈ addRow M S, ∀ i, r (rep i) = r i := fun r hr i => congrFun (hcol_rep i) ⟨r, hr⟩
  have hvalM : ∀ r ∈ M, ∀ i, r (rep i) = r i := fun r hr => hval r (mem_addRow.2 (Or.inr hr))
  have hvalS : ∀ i, S (rep i) = S i := hval S (mem_addRow.2 (Or.inl rfl))
  set A : Set ι := Set.range rep with hA
  have hrepA : ∀ a : A, rep a.1 = a.1 := by
    rintro ⟨_, i, rfl⟩
    exact hrep_rep i
  set ρ : ι → A := fun i => ⟨rep i, i, rfl⟩ with hρ
  have hρA : ∀ a : A, ρ a.1 = a := fun a => Subtype.ext (hrepA a)
  set MA := restrictRows A M with hMA
  set SA := A.domRestrict S with hSA
  have hMAne : MA.Nonempty := by
    obtain ⟨r, hr⟩ := hM
    exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
  have hCA : NoConstantColumn MA := hC.restrictRows A
  -- `M + S` on `A`.
  have hadd : addRow MA SA = (addRow M S).image A.domRestrict := by
    simp only [addRow, hMA, restrictRows, Finset.image_insert, hSA]
  have hinjOn : Set.InjOn A.domRestrict (addRow M S : Set (ι → Bool)) := by
    intro r hr r' hr' hrr
    funext i
    have h₁ := congrFun hrr (ρ i)
    change r (rep i) = r' (rep i) at h₁
    rw [hval r hr i, hval r' hr' i] at h₁
    exact h₁
  have hcard : (addRow MA SA).card = (addRow M S).card := by
    rw [hadd]
    exact Finset.card_image_of_injOn hinjOn
  have hinjA : Function.Injective fun a : A => fun r : addRow MA SA => (r : A → Bool) a := by
    intro a b hab
    have hcolab : col a.1 = col b.1 := by
      funext r
      have := congrFun hab ⟨A.domRestrict r.1, by rw [hadd]; exact Finset.mem_image_of_mem _ r.2⟩
      exact this
    exact Subtype.ext ((hrepA a).symm.trans ((hrep_eq hcolab).trans (hrepA b)))
  have hdist : distinctColumns (addRow MA SA) = distinctColumns (addRow M S) := by
    rw [distinctColumns, distinctColumns, Set.ncard_range_of_injective hinjA]
    have himg : col '' A = Set.range col := by
      ext f
      constructor
      · rintro ⟨_, -, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨rep i, ⟨i, rfl⟩, hcol_rep i⟩
    have hinjcol : Set.InjOn col A := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      rw [← hrep_rep i, ← hrep_rep j]
      exact hrep_eq hij
    change A.ncard = (Set.range col).ncard
    rw [← himg, hinjcol.ncard_image]
  have hH : haplotypeBound (addRow MA SA) = haplotypeBound (addRow M S) := by
    rw [haplotypeBound, haplotypeBound, hcard, hdist]
  -- `R_S(M)` on `A`.
  have hle : RS .multiple SA MA ≤ RS .multiple S M := by
    obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := Nat.sInf_mem (rootedRecombSet_nonempty .multiple S hM)
    change N.recombCount = RS .multiple S M at hcount
    rw [← hcount]
    refine (hS ▸ Network.RS_le_card_breaksAt hc hd hC A : RS .multiple (A.domRestrict S) (restrictRows A M) ≤ _).trans
      (Set.ncard_le_ncard (s := {x | N.IsRecomb x ∧ N.BreaksAt x A}) (t := {x | N.IsRecomb x}) (fun x hx => hx.1) (Set.toFinite _))
  have hge := MyersGriffiths2003.haplotypeBound_addRow_le_RS .multiple SA MA hMAne
  have heq : haplotypeBound (addRow MA SA) = RS .multiple SA MA := by
    rw [hH, h] at hge ⊢
    exact le_antisymm hge (by exact_mod_cast hle)
  have heqR : RS .multiple SA MA = RS .multiple S M := by
    rw [hH, h] at heq
    exact_mod_cast heq.symm
  obtain ⟨a, b, N₁, hc₁, hd₁, hS₁, hfd, hcount₁⟩ := sMinDecomposable_of_haplotype_tight hMAne hCA hinjA heq
  -- The graphs.
  set G := conflictGraph S M with hG
  set GA := conflictGraph SA MA with hGA
  have hAdjA : ∀ a b : A, GA.Adj a b ↔ G.Adj a.1 b.1 := by
    intro a b
    change Conflict SA MA a b ↔ Conflict S M a.1 b.1
    constructor
    · intro hab x y hxy
      obtain ⟨r, hr, h₁, h₂⟩ := hab x y hxy
      obtain ⟨r', hr', rfl⟩ := mem_restrictRows.1 hr
      exact ⟨r', hr', h₁, h₂⟩
    · intro hab x y hxy
      obtain ⟨r, hr, h₁, h₂⟩ := hab x y hxy
      exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩, h₁, h₂⟩
  have hAdjRep : ∀ i j, G.Adj i j ↔ G.Adj (rep i) (rep j) := by
    intro i j
    rw [hG, conflictGraph_eq_incompatGraph_addRow]
    change Incompatible _ i j ↔ Incompatible _ (rep i) (rep j)
    refine forall₂_congr fun x y => exists_congr fun r => and_congr_right fun hr => ?_
    rw [hval r hr i, hval r hr j]
  have hAdjρ : ∀ i j, G.Adj i j ↔ GA.Adj (ρ i) (ρ j) := fun i j => (hAdjRep i j).trans (hAdjA (ρ i) (ρ j)).symm
  have hAdjMap : ∀ {a b : A}, GA.Reachable a b → G.Reachable a.1 b.1 := by
    intro a b hab
    rw [SimpleGraph.reachable_iff_reflTransGen] at hab
    induction hab with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hbc ih => exact ih.trans (SimpleGraph.Adj.reachable ((hAdjA _ _).1 hbc))
  refine ⟨a, b, N₁.liftSites ρ, trivial, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, hcount₁.trans heqR⟩
  -- `Derives M`.
  · intro v hv
    obtain ⟨r, hr, hrv⟩ := mem_restrictRows.1 (hd₁.mapsTo hv)
    have : (N₁.liftSites ρ).label v = r := by
      funext i
      change N₁.label v (ρ i) = r i
      rw [← hrv]
      exact hvalM r hr i
    rw [this]
    exact hr
  · intro v hv w hw hvw
    refine hd₁.injOn hv hw (funext fun x => ?_)
    have := congrFun hvw x.1
    change N₁.label v (ρ x.1) = N₁.label w (ρ x.1) at this
    rwa [hρA] at this
  · intro r hr
    obtain ⟨v, hv, hrv⟩ := hd₁.surjOn (mem_restrictRows.2 ⟨r, hr, rfl⟩)
    refine ⟨v, hv, funext fun i => ?_⟩
    change N₁.label v (ρ i) = r i
    rw [hrv]
    exact hvalM r hr i
  -- The ancestral sequence.
  · funext i
    change N₁.label N₁.root (ρ i) = S i
    have := congrFun hS₁ (ρ i)
    change N₁.label N₁.root (ρ i) = S (rep i) at this
    rw [this, hvalS]
  -- Fully decomposed.
  · intro B hB
    obtain ⟨cA, hnt, hmem⟩ := hfd.blob_component B ((Network.isBlob_liftSites N₁ ρ B).1 hB)
    obtain ⟨a₀, ha₀⟩ := cA.nonempty_supp
    have hK₁ : ∀ a ∈ cA.supp, G.Reachable a₀.1 a.1 := fun a ha => hAdjMap (cA.reachable_of_mem_supp ha₀ ha)
    have hK₂ : ∀ i, ρ i ∈ cA.supp → G.Reachable (rep i) i := by
      intro i hi
      obtain ⟨b', hb', hne⟩ := hnt.exists_ne (ρ i)
      obtain ⟨p⟩ := cA.reachable_of_mem_supp hi hb'
      cases p with
      | nil => exact absurd rfl hne
      | @cons _ c _ hadj _ =>
        have h₁ : G.Adj (rep i) c.1 := (hAdjA _ _).1 hadj
        have h₂ : G.Adj i c.1 := by
          rw [hAdjRep, hrepA]
          exact h₁
        exact (SimpleGraph.Adj.reachable h₁).trans (SimpleGraph.Adj.reachable h₂).symm
    have hK₃ : ∀ i, G.Reachable a₀.1 i → ρ i ∈ cA.supp := by
      intro i hi
      rw [SimpleGraph.reachable_iff_reflTransGen] at hi
      induction hi with
      | refl => rwa [hρA]
      | tail _ hbc ih =>
        have : GA.Reachable _ _ := SimpleGraph.Adj.reachable ((hAdjρ _ _).1 hbc)
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ih ⊢
        rw [← ih]
        exact SimpleGraph.ConnectedComponent.sound this.symm
    refine ⟨G.connectedComponentMk a₀.1, ?_, fun i => ?_⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := hnt
      refine ⟨x.1, ?_, y.1, ?_, fun h' => hxy (Subtype.ext h')⟩
      · rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact SimpleGraph.ConnectedComponent.sound (hK₁ x hx).symm
      · rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact SimpleGraph.ConnectedComponent.sound (hK₁ y hy).symm
    · rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      change N₁.site (ρ i) ∈ B ↔ _
      rw [hmem]
      constructor
      · intro hi
        exact SimpleGraph.ConnectedComponent.sound ((hK₁ _ hi).trans (hK₂ i hi)).symm
      · intro hi
        exact hK₃ i (SimpleGraph.ConnectedComponent.exact hi).symm
  · intro i hi
    refine (Network.isTreeArc_liftSites N₁ ρ _).2 (hfd.isolated_treeArc (ρ i) fun b hb => ?_)
    have h₁ : G.Adj (rep i) b.1 := (hAdjA _ _).1 hb
    exact hi b.1 (by rw [hAdjRep, hrepA]; exact h₁)
  · exact (Network.blobsNodeDisjoint_liftSites N₁ ρ).2 hfd.nodeDisjoint

/-- **Theorem 10, with the ancestral sequence** (`g:thm10`). The proof at lines 560 to 564 is for this form: if `H(M + S) = R¹_S(M)` then `M` is S-min-1 decomposable, and if `H(M + S) = R_S(M)` then `M` is S-min decomposable. Departure from the paper: `R¹_S(M)`, `R_S(M)` in place of
`R¹(M + S)`, `R(M + S)`, because the proof's network has ancestral sequence `S`; and, for `single` only, distinct columns in `M + S`, because the equality case at line 560 needs them (`g:visible_false`). For `multiple` the hypothesis isn't needed, by `theorem10_multiple`, and for the recombinations that model
back and recurrent mutation it isn't either, by Corollary 3. Whether it can be dropped for `single` is open: re-inserting a duplicate site on its representative's arc can break the prefix-suffix form of a crossover between them. -/
theorem theorem10 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hinj : c = .single → Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := by
  cases c
  · exact sMinDecomposable_of_haplotype_tight hM hC (hinj rfl) h
  · exact theorem10_multiple hM hC h
  · exact (corollary3 M S hM hC).1

section Theorem6

universe w

variable {V' : Type*}

omit [LinearOrder ι] in
/-- In a network with every node visible and each arc with at most one site, either the count of the proof of Theorem 6 holds, or a recombination node has the label of a node not below it. These are the cases of the
modification at line 576. The two conditions of line 576 don't exclude a recombination node labelled `S`, and with one the count of the proof of Theorem 6 is off by one: this case is among those moved here, under the root. The label of the target of
an arc with a site isn't that of the root, and two such targets don't have the same label, unless the site is the same (`he`); a recombination node with one of those labels is below that target. -/
theorem exists_reattach_of_card_lt {E' : Type*} {M : Finset (ι → Bool)} {S : ι → Bool} [Finite V'] (N : Network ι V' E') (hv : N.AllVisible M S)
    (he : Function.Injective N.site) (hlt : (addRow M S).card < N.recombCount + Nat.card ι + 1) :
    ∃ x y, N.IsRecomb x ∧ N.label y = N.label x ∧ ¬ N.Reach x y := by
  set φ : Option (ι ⊕ {x // N.IsRecomb x}) → addRow M S := fun a =>
    ⟨N.label (match a with
      | none => N.root
      | some (.inl i) => N.tgt (N.site i)
      | some (.inr x) => x.1), hv _⟩ with hφ
  have hnoninj : ¬ Function.Injective φ := by
    intro hinj
    have := Nat.card_le_card_of_injective φ hinj
    rw [Finite.card_option, Nat.card_sum, show Nat.card (addRow M S) = (addRow M S).card by simp] at this
    have h₁ : Nat.card {x // N.IsRecomb x} = N.recombCount := rfl
    omega
  rw [Function.Injective] at hnoninj
  push Not at hnoninj
  obtain ⟨a, b, hab, hne⟩ := hnoninj
  have hab' := congrArg Subtype.val hab
  have hhead : ∀ i, N.label (N.tgt (N.site i)) i ≠ N.label N.root i := N.label_tgt_site_ne
  have hreachHead : ∀ i y, N.label y = N.label (N.tgt (N.site i)) → N.Reach (N.tgt (N.site i)) y := fun i y hy =>
    N.reach_of_label_ne (by rw [hy]; exact hhead i)
  have hrootCase : ∀ x, N.IsRecomb x → ¬ N.Reach x N.root := fun x hx h =>
    Network.not_isRecomb_root (Network.eq_root_of_reach h ▸ hx)
  have hheadCase : ∀ i x, N.IsRecomb x → N.label x = N.label (N.tgt (N.site i)) → ¬ N.Reach x (N.tgt (N.site i)) := fun i x hx hl h => by
    have := Network.Reach.antisymm h (hreachHead i x hl)
    exact Network.not_isRecomb_tgt_site i (this ▸ hx)
  rcases a with - | a | a <;> rcases b with - | b | b
  · exact absurd rfl hne
  · have h₁ : N.label N.root = N.label (N.tgt (N.site b)) := hab'
    exact absurd (congrFun h₁ b).symm (hhead b)
  · have h₁ : N.label N.root = N.label b.1 := hab'
    exact ⟨b.1, N.root, b.2, h₁, hrootCase _ b.2⟩
  · have h₁ : N.label (N.tgt (N.site a)) = N.label N.root := hab'
    exact absurd (congrFun h₁ a) (hhead a)
  · have h₁ : N.label (N.tgt (N.site a)) = N.label (N.tgt (N.site b)) := hab'
    have h₂ := Network.Reach.antisymm (hreachHead a _ h₁.symm) (hreachHead b _ h₁)
    have h₃ : N.site b = N.site a := N.site_not_recomb a (N.site b) h₂.symm
    exact absurd (by rw [he h₃]) hne
  · have h₁ : N.label (N.tgt (N.site a)) = N.label b.1 := hab'
    exact ⟨b.1, _, b.2, h₁, hheadCase a _ b.2 h₁.symm⟩
  · have h₁ : N.label a.1 = N.label N.root := hab'
    exact ⟨a.1, N.root, a.2, h₁.symm, hrootCase _ a.2⟩
  · have h₁ : N.label a.1 = N.label (N.tgt (N.site b)) := hab'
    exact ⟨a.1, _, a.2, h₁.symm, hheadCase b _ a.2 h₁⟩
  · have h₁ : N.label a.1 = N.label b.1 := hab'
    have hne' : a.1 ≠ b.1 := fun h => hne (by rw [Subtype.ext h])
    by_cases hr : N.Reach a.1 b.1
    · exact ⟨b.1, a.1, b.2, h₁, fun h => hne' (Network.Reach.antisymm hr h)⟩
    · exact ⟨a.1, b.1, a.2, h₁.symm, hr⟩

/-- The modification at the start of the proof of Theorem 6 (line 576), in the form of the count that it's used for: "`R(N)` must be exactly the number of sequences in `M + S`, minus the number of labeled edges in `N`, minus 1". As long as there are more recombination nodes than the count allows, one of them
can be moved under a node with its label. Line 576 also asks that the target of an arc with a site have a label on no other node. Taken literally this is more than can be had, as a node reached by an arc with no site can have that label, and it isn't needed: only recombination nodes have to move, and the count is `≤`. -/
theorem exists_tight_of_allVisible {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} [Finite V'] :
    ∀ (n : ℕ) (E₁ : Type w) [Finite E₁] (N : Network ι V' E₁), N.recombCount = n → N.Obeys c → (∀ r ∈ M, ∃ v, N.label v = r) → N.ancestral = S →
      N.AllVisible M S → Function.Injective N.site →
      ∃ (E₂ : Type w) (_ : Finite E₂) (N' : Network ι V' E₂), N'.Obeys c ∧ (∀ r ∈ M, ∃ v, N'.label v = r) ∧ N'.ancestral = S ∧
        N'.recombCount + Nat.card ι + 1 ≤ (addRow M S).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E₁ _ N hn hc hd hS hv he
    by_cases htight : N.recombCount + Nat.card ι + 1 ≤ (addRow M S).card
    · exact ⟨E₁, inferInstance, N, hc, hd, hS, htight⟩
    · obtain ⟨x, y, hx, hy, hr⟩ := exists_reattach_of_card_lt N hv he (not_le.1 htight)
      obtain ⟨e, f, hef, rfl, hf⟩ := hx
      have he' : N.tgt e = N.tgt f := hf.symm
      have hlt := Network.recombCount_reattach_lt (N := N) (hef := hef) (he := he') (hl := hy) (hy := hr)
      exact ih _ (hn ▸ hlt) {g // g ≠ f} (N.reattach hef he' hy hr) rfl (Network.obeys_reattach hc) hd hS hv
        fun i j hij => he (congrArg Subtype.val hij)

end Theorem6

/-- **Theorem 6** (`g:thm6`). "Let `N` be a phylogenetic network (which might not be optimal) for `M` with ancestral sequence `S`. Then `M` is S-min or S-min-1 decomposable
(depending on the type of crossovers used in `N`), if every node in `N` is visible, and every edge in `N` is labeled by at most one site" (line 449).

A network using only single crossovers also obeys `multiple`, and then the proof gives both conclusions. The columns of `M + S` are distinct under these hypotheses, so `theorem10` applies. The proof of the paper modifies `N` first (line 576), and that part is
`exists_tight_of_allVisible`; the count is an inequality here, which is enough. -/
theorem theorem6 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S) (hv : N.AllVisible M S)
    (he : Function.Injective N.site) : SMinDecomposable c S M := by
  have hM := hd.nonempty
  obtain ⟨E₂, _, N₁, hc₁, hd₁, hS₁, htight⟩ := exists_tight_of_allVisible _ E N rfl hc hd.displays hS hv he
  obtain ⟨a, b, N₂, h₁, h₂, h₃, h₄⟩ := Network.exists_derives_of_displays N₁ hM hC hd₁
  have hle : RS c S M ≤ N₁.recombCount := (RS_le_recombCount N₂ (h₁ c hc₁) h₂ (h₃.trans hS₁)).trans h₄
  have hH := MyersGriffiths2003.haplotypeBound_addRow_le_RS c S M hM
  have hdistle : distinctColumns (addRow M S) ≤ Nat.card ι := by
    rw [distinctColumns, ← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by rw [Set.ncard_univ])
  unfold haplotypeBound at hH
  have hdist : distinctColumns (addRow M S) = Nat.card ι := by omega
  have hinj : Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i := by
    rw [← Set.injOn_univ, ← Set.ncard_image_iff Set.finite_univ, Set.image_univ, Set.ncard_univ]
    exact hdist
  refine theorem10 hM hC (fun _ => hinj) ?_
  unfold haplotypeBound
  omega

end Gusfield2007
