module

public import Gusfield2007.Conjectures
public import External.MyersGriffiths2003.Bound

/-!
# Gusfield et al. 2007, Section 5.2: sufficient conditions for `M` to be S-min or S-min-1 decomposable

Lemma 5, Theorem 7, Corollary 3, Theorem 8, Theorem 9, Theorem 5, Corollary 2, Theorem 10, Theorem 6, in the order of their
proofs. A statement with a crossover model `c` covers the two cases of the paper (`c = multiple`, `c = single`), and the model of
back and recurrent mutation that Corollary 3 needs.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E]

/-- **Lemma 5** (`g:lem5`). "Let `N` be an arbitrary phylogenetic network for `M` with ancestral sequence `S`, and suppose that every
recombination in `N` is either a 0 or 1-component recombination. [...] If multiple-crossover recombinations are allowed in `N`, then
`R(N) ≥ Σ_{C ∈ G_S(M)} R_{S(C)}(M(C))`, and if only single-crossover recombinations are allowed, then `R(N) ≥ Σ_{C ∈ G_S(M)} R¹_{S(C)}(M(C))`" (line 463).

The standing assumption is needed. With `M = {00} = {S}`, a network with one recombination node derives `M` by flipping both sites on one
arc and then taking the root's sequence, and it's a 0-component recombination; each of the two trivial components needs one
recombination node on its own, since its site must mutate and come back. So the sum is 2. -/
theorem lemma5 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) ≤ N.recombCount := by
  sorry

/-- **Theorem 7** (`g:thm7`). "Let `N` be a phylogenetic network for `M` with ancestral sequence `S` such that every recombination node in `N` is
either a 0 or 1-component recombination node, relative to `G_S(M)`. Then there is fully-decomposed phylogenetic network `N'` for `M`, with ancestral
sequence `S`, using at most `R(N)` recombination nodes, where both `N` and `N'` allow the same type of recombinations" (line 492). -/
theorem theorem7 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount := by
  sorry

/-- **Bridge for Corollary 3** (`g:parsimony_bridge`). Each mutation beyond the first at a site is one recombination modelling it (lines 358, 511):
the parsimony score with ancestral sequence `S` is the number of sites plus `R_S(M)` in the model of back and recurrent mutation. The
standing assumption is needed: a constant column at the state of `S` costs no mutation, but it must mutate on a network. -/
theorem parsimonyScore_eq (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    parsimonyScore S M = Nat.card ι + RS .pointwise S M := by
  sorry

/-- **Corollary 3** (`g:cor3`). "When recombinations only model back or recurrent mutations (as detailed in Section 4.1), then `M` is S-min
decomposable for any sequence `S`, and the maximum parsimony problem for `M` can be solved by separately solving a maximum parsimony problem for
the sites from each connected component of `G_S(M)`" (line 506).

"S-min decomposable" is in the model of those recombinations: it can't be for `multiple`, by `g:multiple_false`. -/
theorem corollary3 (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    SMinDecomposable .pointwise S M ∧
      parsimonyScore S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) := by
  sorry

/-- **Line 411** (`g:mutation_min`). "When the recombination events only model recurrent and back mutations, then every `M` is min decomposable." The
paper proves a specialization (Corollary 3), and refers to Bandelt et al. 1995 for this. An argument from Corollary 3: the parsimony score doesn't
change on re-rooting at a row of an optimal tree, so an optimal `S` can be taken in `M`, where `G_S(M) = G(M)`. -/
theorem minDecomposable_pointwise (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    MinDecomposable .pointwise M := by
  sorry

/-- **Theorem 8** (`g:thm8`). "Given `S`, if `M` is spatially disjoint, then `M` is S-min-1 decomposable" (line 519).

A misprint in the proof, at line 525: "using `R¹(M + S)` single-crossover recombinations" should be `R¹_S(M)`, since the network is for `M` with
ancestral sequence `S`, and the two can differ. -/
theorem theorem8 {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : SpatiallyDisjoint S M) : SMinDecomposable .single S M := by
  sorry

/-- **Line 533** (`g:respects_iff`). "Since `M + S ⊆ L`, any incompatible pair in `M + S` is incompatible in `L`, so `L` respects `G_S(M)` if and only if
`G_S(L)` and `G_S(M)` have the same number of components". -/
theorem respects_iff_card {L M : Finset (ι → Bool)} {S : ι → Bool} (h : addRow M S ⊆ L) :
    Respects L S M ↔
      Nat.card (conflictGraph S L).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent := by
  sorry

/-- **Theorem 9** (`g:thm9`). "Let `N` be a phylogenetic network for `M` with ancestral sequence `S`, and suppose that `L` respects `G_S(M)`. Then there is
fully-decomposed phylogenetic network `N'` for `M`, with ancestral sequence `S`, using at most `R(N)` recombination nodes, where `N` and `N'` allow the
same type of recombinations" (line 538). -/
theorem theorem9 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S) (h : Respects N.labelSet S M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount := by
  sorry

/-- **Theorem 5** (`g:thm5`). "Let `N` be an optimal phylogenetic network for `M` with ancestral sequence `S`, allowing multiple-crossover recombination
(respectively allowing only single-crossover recombination), using `R_S(M)` (respectively `R¹_S(M)`) recombination nodes. Let `G_S(L)` be the conflict graph
for sequences `L` with respect to `S`. Then `M` is S-min (respectively S-min-1) decomposable if `G_S(M)` and `G_S(L)` have the same number of connected
components" (line 432). -/
theorem theorem5 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hN : N.IsOptimalRooted c S M)
    (h : Nat.card (conflictGraph S N.labelSet).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent) :
    SMinDecomposable c S M := by
  sorry

/-- **Corollary 2** (`g:cor2`). "Let `N` be an optimal phylogenetic network for `M` with ancestral sequence `S`, allowing multiple-crossover recombination
(respectively allowing only single-crossover recombination). Then `M` is S-min (respectively S-min-1) decomposable, if every node in `N` is visible"
(line 440). A visible node is one labelled by a row of `M`; in the rooted case that means `L = M + S` (line 427). -/
theorem corollary2 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hN : N.IsOptimalRooted c S M) (h : N.AllVisible M S) : SMinDecomposable c S M := by
  sorry

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

This is doubtful as printed, and it's neither proved nor refuted here. Its proof reasons on an optimal network for `M` with ancestral sequence `S`, using `R_S(M)` nodes, and treats that number
as `R(M + S)`, the minimum over all ancestral sequences (lines 560 to 563). They can differ under the hypothesis: for `M + S = {0000, 0101, 1000, 1010, 1110, 1111}` and `S = 0101`, with multiple
crossovers, `H(M + S) = R(M + S) = 1` and `R_S(M) = 2`. If `R_S(M) > R(M + S)`, the tight network has another root, and the proof doesn't apply. That example has one component, so the conclusion holds;
a search for an example with two components, where the conclusion fails, found none. The form with `R_S(M)` is `theorem10`, which is what the proof of Theorem 6 needs. -/
def Theorem10Printed (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) : Prop :=
  haplotypeBound (addRow M S) = R c (addRow M S) → SMinDecomposable c S M

/-- **Theorem 10, with the ancestral sequence** (`g:thm10`). The proof at lines 560 to 564 is for this form: if `H(M + S) = R¹_S(M)` then `M` is S-min-1 decomposable, and if
`H(M + S) = R_S(M)` then `M` is S-min decomposable. Departure from the paper: `R¹_S(M)`, `R_S(M)` in place of `R¹(M + S)`, `R(M + S)`, and distinct columns in `M + S`, because
the equality case at line 560 needs them (`g:visible_false`). -/
theorem theorem10 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (hinj : Function.Injective fun i : ι => fun r : addRow M S => (r : ι → Bool) i)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := by
  sorry

/-- **Theorem 6** (`g:thm6`). "Let `N` be a phylogenetic network (which might not be optimal) for `M` with ancestral sequence `S`. Then `M` is S-min or S-min-1 decomposable
(depending on the type of crossovers used in `N`), if every node in `N` is visible, and every edge in `N` is labeled by at most one site" (line 449).

A network using only single crossovers also obeys `multiple`, and then the proof gives both conclusions. The columns of `M + S` are distinct under these hypotheses, so `theorem10` applies. -/
theorem theorem6 {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E)
    (hc : N.Obeys c) (hd : N.Derives M) (hS : N.ancestral = S) (hv : N.AllVisible M S)
    (he : Function.Injective N.site) : SMinDecomposable c S M := by
  sorry

end Gusfield2007
