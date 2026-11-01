module

public import Gusfield2007.Uniqueness

/-!
# Gusfield et al. 2007, Section 5.1: the Full-Decomposition Optimality Conjectures

The relations between the four conjectures, and the computation of `F` and `F_S`. The conjectures
themselves are in `Gusfield2007.Defs`, and their refutations in `Gusfield2007.Counterexamples`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [LinearOrder ι] [Finite ι]

omit [LinearOrder ι] [Finite ι] in
/-- The components of two graphs with the same reachability are the same sets of sites. -/
def ccEquiv {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j) :
    G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun C := C.lift (fun i => G'.connectedComponentMk i) fun _ _ p _ =>
    SimpleGraph.ConnectedComponent.eq.2 ((h _ _).1 p.reachable)
  invFun C := C.lift (fun i => G.connectedComponentMk i) fun _ _ p _ =>
    SimpleGraph.ConnectedComponent.eq.2 ((h _ _).2 p.reachable)
  left_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind
    rfl
  right_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind
    rfl

omit [LinearOrder ι] [Finite ι] in
theorem ccEquiv_supp {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j) (C : G.ConnectedComponent) :
    (ccEquiv h C).supp = C.supp := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ i₀ =>
    ext i
    change i ∈ (G'.connectedComponentMk i₀).supp ↔ i ∈ (G.connectedComponentMk i₀).supp
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact (h i i₀).symm

omit [LinearOrder ι] [Finite ι] in
/-- A sum over the components of a graph depends only on the components, as sets of sites. -/
theorem finsum_connectedComponent_congr {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j) (g : Set ι → ℕ) :
    ∑ᶠ C : G.ConnectedComponent, g C.supp = ∑ᶠ C : G'.ConnectedComponent, g C.supp := by
  rw [← finsum_comp_equiv (ccEquiv h)]
  exact finsum_congr fun C => by rw [ccEquiv_supp]

/-- **Line 413** (`g:compute_FS`). "Even if `M` is not S-min or S-min-1 decomposable, this method will find the minimum number of
recombination nodes, denoted `F_S(M)` and `F¹_S(M)`, used in any fully decomposed network for `M` with ancestral sequence `S`". The bound `≤` is Theorem 3. The bound `≥` is Lemma 5: in a fully decomposed network each recombination node is a 0 or 1-component recombination. -/
theorem FS_eq_sum (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    FS c S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  obtain ⟨a, b, N, h₁, h₂, h₃, h₄, h₅⟩ := theorem3 c M S hM hC
  refine le_antisymm (Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, h₄, h₅⟩) ?_
  obtain ⟨a', b', N', h₁', h₂', h₃', h₄', h₅'⟩ :=
    Nat.sInf_mem (s := {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧ N.recombCount = k}) ⟨_, a, b, N, h₁, h₂, h₃, h₄, rfl⟩
  change _ ≤ FS c S M
  rw [FS, ← h₅']
  subst h₃'
  exact lemma5 hC N' h₁' h₂' rfl fun x hx => h₄'.isZero_or_isOne hx

/-- **Line 403** (`g:rooted_equiv`). "The rooted conjectures are equivalent to the conjectures that
`R_S(M) = Σ_{C ∈ G_S(M)} R_{S(C)}(M(C))` and `R¹_S(M) = Σ_{C ∈ G_S(M)} R¹_{S(C)}(M(C))`". -/
theorem sMinDecomposable_iff (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    SMinDecomposable c S M ↔
      RS c S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  obtain ⟨a, b, N, h₁, h₂, h₃, h₄, h₅⟩ := theorem3 c M S hM hC
  constructor
  · rintro ⟨a', b', N', h₁', h₂', h₃', h₄', h₅'⟩
    refine le_antisymm (h₅ ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, rfl⟩) ?_
    rw [← h₅']
    subst h₃'
    exact lemma5 hC N' h₁' h₂' rfl fun x hx => h₄'.isZero_or_isOne hx
  · intro h
    exact ⟨a, b, N, h₁, h₂, h₃, h₄, h₅.trans h.symm⟩

/-- **Line 635** (`g:F_ge_sum`). "Clearly, `F¹(M) ≥ Σ_{C ∈ G(M)} R¹(M(C))`". -/
theorem sum_R_le_F (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∑ᶠ C : (incompatGraph M).ConnectedComponent, R c (restrictRows C.supp M) ≤ F c M := by
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
  obtain ⟨a', b', N', h₁', h₂', h₃', h₄'⟩ :=
    Nat.sInf_mem (s := {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) ∧ N.recombCount = k}) ⟨_, a, b, N, h₁, h₂, h₃, rfl⟩
  rw [F, ← h₄']
  have hreach := reachable_conflictGraph_iff h₂' h₃'
  have hfS := h₃'.of_reachable_iff fun i j => (hreach i j).symm
  have h5 := lemma5 hC N' h₁' h₂' rfl fun x hx => hfS.isZero_or_isOne hx
  rw [finsum_connectedComponent_congr hreach (fun s => RS c (s.domRestrict N'.ancestral) (restrictRows s M))] at h5
  refine le_trans ?_ h5
  have : Fintype (incompatGraph M).ConnectedComponent := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_le_sum fun C _ => R_le_RS c _ ?_
  obtain ⟨r, hr⟩ := hM
  exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩

omit [Finite ι] in
/-- **Line 403** (`g:rooted_implies_unrooted`), one input at a time, in the form that the paper's sentence proves: "letting `S` be the
ancestral sequence that appears in the optimal phylogenetic network using `R(M)` recombination nodes". The hypothesis `hG`, that `G_S(M)`
has the components of `G(M)`, is an addition, and it's necessary. Without it, the network that S-min decomposability gives is fully decomposed with
respect to `G_S(M)`, not `G(M)`. In Figure 6, Figure 7's topology with the root relabelled `001100` gives `R¹_S(M) = 3 = R¹(M)` with `G_S(M)` connected, so `M` is S-min-1 decomposable there, yet `F¹(M) = 4`, and so `M` isn't min-1 decomposable. That example is proved
as `fig6_hG_necessary`. So the step at line 403 is false on one `(M, S)`, not only a gap. Line 425, "when `M` is S-min decomposable for all `S`, then `M` is min-decomposable", is `MinDecomposableOfForallS`, open here. Between the conjectures, the implication holds because the rooted ones are false:
`rootedConjecture_imp_unrootedConjecture`. -/
theorem minDecomposable_of_sMinDecomposable {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (h : SMinDecomposable c S M) (hopt : RS c S M = R c M)
    (hG : ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) : MinDecomposable c M := by
  obtain ⟨a, b, N, h₁, h₂, -, h₄, h₅⟩ := h
  exact ⟨a, b, N, h₁, h₂, h₄.of_reachable_iff hG, h₅.trans hopt⟩

/-- The sentence at line 425, on one `M`: "when `M` is S-min (respectively S-min-1) decomposable for all `S`, then `M` is
min-decomposable (respectively min-1 decomposable)". Its proof at line 403 has a gap, and we have no counterexample. -/
def MinDecomposableOfForallS (c : Crossover) (M : Finset (ι → Bool)) : Prop :=
  (∀ S, SMinDecomposable c S M) → MinDecomposable c M

/-- **Line 420** (`g:lower_bound_sum`). "When the appropriate conjecture holds for an input `M`, we can also compute lower bounds on `R(M)`,
`R¹(M)` [...] by computing bounds separately for each `M(C)`, adding these bounds together for a valid overall lower bound." -/
theorem sum_R_le_of_minDecomposable {c : Crossover} {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : MinDecomposable c M) : ∑ᶠ C : (incompatGraph M).ConnectedComponent, R c (restrictRows C.supp M) ≤ R c M := by
  obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := h
  exact (sum_R_le_F c M hM hC).trans (h₄ ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, rfl⟩)

section ComputeF

variable {W : Type*}

/-- The cost of the component `C`, for the root placed at the node `v` of `T̄` (line 416). If `v` is on the 1-side of a character
of `C`, its super-character is the ancestral sequence of the blob of `C`, and the cost is a rooted problem; otherwise `v` is the
centre `v_C`, and the ancestral sequence of the blob is free. A non-trivial `C` has at most one such character, by Lemma 4, and a
trivial `C` has cost zero either way. -/
def rootCost (c : Crossover) (M : Finset (ι → Bool)) (T : SimpleGraph W) (φ : M → W) (edge : SuperChar M → Sym2 W) (v : W)
    (C : (incompatGraph M).ConnectedComponent) : ℕ :=
  if h : ∃ (S₀ : C.supp → Bool) (hS₀ : S₀ ∈ restrictRows C.supp M) (r : M),
      charValue (⟨C, ⟨S₀, hS₀⟩⟩ : SuperChar M) r = true ∧ SameSide T (edge ⟨C, ⟨S₀, hS₀⟩⟩) (φ r) v then
    RS c h.choose (restrictRows C.supp M)
  else R c (restrictRows C.supp M)

/-- **`g:compute_F_roots`**, a form of `g:compute_F` without `T̄`. A network fully decomposed for `G(M)`, with ancestral sequence `S`, has
`G_S(M)` with the components of `G(M)` by the converse, and for such `S`, `F_S(M)` is the sum. So `F(M)` is the minimum of the sums over such
`S`. -/
theorem F_eq_sInf_roots (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    F c M = sInf {k | ∃ S : ι → Bool, (∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) ∧
      k = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M)} := by
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
  obtain ⟨a', b', N', h₁', h₂', h₃', h₄'⟩ :=
    Nat.sInf_mem (s := {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) ∧ N.recombCount = k}) ⟨_, a, b, N, h₁, h₂, h₃, rfl⟩
  have hopt : (N'.recombCount : ℕ) = F c M := h₄'
  have hN' := reachable_conflictGraph_iff h₂' h₃'
  apply le_antisymm
  · refine le_csInf ⟨_, N.ancestral, reachable_conflictGraph_iff h₂ h₃, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    obtain ⟨a₁, b₁, N₁, h₁₁, h₂₁, -, h₄₁, h₅₁⟩ := theorem3 c M S hM hC
    exact h₅₁ ▸ Nat.sInf_le ⟨a₁, b₁, N₁, h₁₁, h₂₁, h₄₁.of_reachable_iff hS, rfl⟩
  · refine csInf_le_of_le (OrderBot.bddBelow _) ⟨N'.ancestral, hN', rfl⟩ ?_
    rw [← hopt]
    exact lemma5 hC N' h₁' h₂' rfl fun x hx => (h₃'.of_reachable_iff fun i j => (hN' i j).symm).isZero_or_isOne hx

/-! ### The sides of `T̄`, for the root -/

/-- A component with at most one site needs no recombination node, for any ancestral sequence: it's Theorem 1 for that component. -/
theorem RS_eq_zero_of_not_nontrivial (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) {C : Set ι} (hnt : ¬ C.Nontrivial) (S : C → Bool) :
    RS c S (restrictRows C M) = 0 := by
  have hL : (restrictRows C M).Nonempty := by
    obtain ⟨r, hr⟩ := hM
    exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
  obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := theorem1_rooted c (restrictRows C M) S hL (hC.restrictRows C)
  have hnoblob : ∀ B, ¬ N.IsBlob B := by
    intro B hB
    obtain ⟨c', ⟨i, -, j, -, hij⟩, -⟩ := h₄.blob_component B hB
    exact hnt ⟨i.1, i.2, j.1, j.2, fun h => hij (Subtype.ext h)⟩
  have hempty : IsEmpty {x // N.IsRecomb x} := ⟨fun ⟨x, e, f, hef, he, hf⟩ => by
    obtain ⟨B, hB, -, -⟩ := Network.exists_isBlob_of_tgt_eq hef (he.trans hf.symm)
    exact hnoblob B hB⟩
  have hzero : N.recombCount = 0 := by simp [Network.recombCount]
  exact Nat.le_zero.1 (hzero ▸ Nat.sInf_le ⟨a, b, N, h₁, h₂, h₃, rfl⟩)

variable {M : Finset (ι → Bool)} {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

variable (T φ edge) in
/-- The node `v` is on the 1-side of the character `k` of `B`. -/
def OnOneSide (k : SuperChar M) (v : W) : Prop :=
  ∃ r : M, charValue k r = true ∧ SameSide T (edge k) (φ r) v

omit [LinearOrder ι] [Finite ι] in
/-- Two characters with `v` on their 1-sides have a common row. It's the fact that the part of `T̄` between two edges has a leaf. -/
theorem IsTBar.exists_row_of_onOneSide [Finite W] (hT : IsTBar M T φ edge) {k k' : SuperChar M} {v : W} (h : OnOneSide T φ edge k v) (h' : OnOneSide T φ edge k' v) :
    ∃ x : M, charValue k x = true ∧ charValue k' x = true := by
  obtain ⟨r, hr, hrv⟩ := h
  obtain ⟨r', hr', hrv'⟩ := h'
  obtain ⟨x, hx, hx'⟩ := exists_label_sameSide hT.isTree hT.labelled (edge k) (edge k') v
  exact ⟨x, ((hT.split k r x).2 (hrv.trans hx)).symm.trans hr, ((hT.split k' r' x).2 (hrv'.trans hx')).symm.trans hr'⟩

omit [LinearOrder ι] [Finite ι] in
/-- A node is on the 1-side of at most one character of a component. -/
theorem IsTBar.eq_of_onOneSide [Finite W] (hT : IsTBar M T φ edge) {k k' : SuperChar M} {v : W} (hk : k.1 = k'.1) (h : OnOneSide T φ edge k v) (h' : OnOneSide T φ edge k' v) :
    k = k' := by
  obtain ⟨x, hx, hx'⟩ := hT.exists_row_of_onOneSide h h'
  obtain ⟨c, S₀, hS₀⟩ := k
  obtain ⟨c', S₁, hS₁⟩ := k'
  obtain rfl : c = c' := hk
  have h₁ : c.supp.domRestrict x.1 = S₀ := by simpa [charValue] using hx
  have h₂ : c.supp.domRestrict x.1 = S₁ := by simpa [charValue] using hx'
  obtain rfl := h₁.symm.trans h₂
  rfl

omit [Finite ι] in
/-- A node is on the 1-side of a character of a trivial component: its two characters split one edge in two. -/
theorem IsTBar.exists_onOneSide_of_trivial [Finite W] (hT : IsTBar M T φ edge) (hC : NoConstantColumn M) {C : (incompatGraph M).ConnectedComponent} (hnt : ¬ C.supp.Nontrivial) (v : W) :
    ∃ k : SuperChar M, k.1 = C ∧ OnOneSide T φ edge k v := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  have hsupp : ∀ j, j ∈ C.supp ↔ j = i := by
    intro j
    constructor
    · intro hj
      by_contra hne
      exact hnt ⟨j, hj, i, hi, hne⟩
    · rintro rfl
      exact hi
  obtain ⟨r₀, hr₀, r₁, hr₁, hne⟩ := hC i
  have hS : ∀ {r : ι → Bool}, r ∈ M → C.supp.domRestrict r ∈ restrictRows C.supp M := fun hr => mem_restrictRows.2 ⟨_, hr, rfl⟩
  have hval : ∀ {r : ι → Bool} (hr : r ∈ M) (x : ι → Bool), charValue (⟨C, ⟨_, hS hr⟩⟩ : SuperChar M) x = decide (x i = r i) := by
    intro r hr x
    simp only [charValue, decide_eq_decide]
    constructor
    · intro h
      exact congrFun h ⟨i, hi⟩
    · intro h
      funext j
      obtain ⟨j, hj⟩ := j
      obtain rfl := (hsupp j).1 hj
      exact h
  have hiff : ∀ {r : ι → Bool} (hr : r ∈ M) (x y : M), SameSide T (edge ⟨C, ⟨_, hS hr⟩⟩) (φ x) (φ y) ↔ x.1 i = y.1 i := by
    intro r hr x y
    rw [← hT.split ⟨C, ⟨_, hS hr⟩⟩ x y, hval hr, hval hr]
    cases x.1 i <;> cases y.1 i <;> cases r i <;> simp
  have hedge : edge ⟨C, ⟨_, hS hr₀⟩⟩ = edge ⟨C, ⟨_, hS hr₁⟩⟩ :=
    edge_eq_of_sameSide_iff hT.isTree hT.labelled (hT.edge_mem _) fun x y => by rw [hiff hr₀, hiff hr₁]
  by_cases hv : SameSide T (edge ⟨C, ⟨_, hS hr₀⟩⟩) (φ ⟨r₀, hr₀⟩) v
  · exact ⟨⟨C, ⟨_, hS hr₀⟩⟩, rfl, ⟨r₀, hr₀⟩, decide_eq_true rfl, hv⟩
  · refine ⟨⟨C, ⟨_, hS hr₁⟩⟩, rfl, ⟨r₁, hr₁⟩, decide_eq_true rfl, ?_⟩
    rw [← hedge]
    refine sameSide_of_not_sameSide hT.isTree.connected (z := φ ⟨r₀, hr₀⟩) (fun h => ?_) (fun h => hv h.symm)
    exact hne ((hiff hr₀ ⟨r₁, hr₁⟩ ⟨r₀, hr₀⟩).1 h).symm

omit [LinearOrder ι] [Finite ι] in
/-- **The centre of a non-trivial component is the only node on no 1-side of its characters** (line 416). -/
theorem IsTBar.eq_center [Finite W] (hT : IsTBar M T φ edge) {C : (incompatGraph M).ConnectedComponent} (hnt : C.supp.Nontrivial) {v₀ v : W}
    (hv₀ : ∀ k : SuperChar M, k.1 = C → v₀ ∈ edge k) (hv₀' : ∀ k : SuperChar M, k.1 = C → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v₀)
    (hnot : ∀ k : SuperChar M, k.1 = C → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) : v = v₀ := by
  by_contra hne
  obtain ⟨u, hu, hus⟩ := SempleSteel2003.exists_adj_reachable_deleteEdges hT.isTree.connected (Ne.symm hne)
  obtain ⟨k, hk₁, hk₂⟩ := adj_center_labelled hT hnt hv₀ hv₀' hu
  obtain ⟨r, hr⟩ := exists_charValue_eq_true k
  have hfar : SameSide T (edge k) u (φ r) := by
    rw [hk₂]
    refine (SempleSteel2003.reachable_deleteEdges_or hT.isTree.connected v₀ u (φ r)).resolve_left fun h => hv₀' k hk₁ r hr ?_
    rw [hk₂]
    exact h.symm
  refine hnot k hk₁ r hr ?_
  rw [hk₂] at hfar ⊢
  exact hfar.symm.trans hus

omit [LinearOrder ι] [Finite ι] in
/-- **The centre of `C'` is on the 1-side of the dominant character of `C` with respect to `(C, C')`.** The rows with a non-dominant super-character of `C'` have the dominant one of `C`, and two of them are in two branches at the centre of `C'`. -/
theorem IsTBar.onOneSide_of_isDominantFor [Finite W] (hT : IsTBar M T φ edge) {C C' : (incompatGraph M).ConnectedComponent} (hne : C ≠ C') (hnt' : C'.supp.Nontrivial)
    {d : C.supp → Bool} {d' : C'.supp → Bool} (hdom : IsDominantFor M C.supp C'.supp d d') {v : W} (hv : ∀ k : SuperChar M, k.1 = C' → v ∈ edge k)
    (hv' : ∀ k : SuperChar M, k.1 = C' → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) (hd : d ∈ restrictRows C.supp M) :
    OnOneSide T φ edge ⟨C, ⟨d, hd⟩⟩ v := by
  have h4 := four_le_card_restrictRows hnt'
  have h3 : 1 < ((restrictRows C'.supp M).erase d').card := by
    have := Finset.pred_card_le_card_erase (s := restrictRows C'.supp M) (a := d')
    omega
  obtain ⟨S₂, hS₂, S₃, hS₃, hne₂₃⟩ := Finset.one_lt_card.1 h3
  obtain ⟨hS₂n, hS₂m⟩ := Finset.mem_erase.1 hS₂
  obtain ⟨hS₃n, hS₃m⟩ := Finset.mem_erase.1 hS₃
  obtain ⟨r₂, hr₂, hr₂S⟩ := mem_restrictRows.1 hS₂m
  obtain ⟨r₃, hr₃, hr₃S⟩ := mem_restrictRows.1 hS₃m
  have hk₂ : C.supp.domRestrict r₂ = d := (corollary1 M hne hdom hr₂).resolve_right fun h => hS₂n (hr₂S.symm.trans h)
  have hk₃ : C.supp.domRestrict r₃ = d := (corollary1 M hne hdom hr₃).resolve_right fun h => hS₃n (hr₃S.symm.trans h)
  have ht₂ : charValue (⟨C, ⟨d, hd⟩⟩ : SuperChar M) r₂ = true := decide_eq_true hk₂
  have ht₃ : charValue (⟨C, ⟨d, hd⟩⟩ : SuperChar M) r₃ = true := decide_eq_true hk₃
  have hss : SameSide T (edge ⟨C, ⟨d, hd⟩⟩) (φ ⟨r₂, hr₂⟩) (φ ⟨r₃, hr₃⟩) := (hT.split _ _ _).1 (ht₂.trans ht₃.symm)
  obtain ⟨y₂, hy₂⟩ := hv ⟨C', ⟨S₂, hS₂m⟩⟩ rfl
  obtain ⟨y₃, hy₃⟩ := hv ⟨C', ⟨S₃, hS₃m⟩⟩ rfl
  have ha₂ : T.Adj v y₂ := by
    have := hT.edge_mem ⟨C', ⟨S₂, hS₂m⟩⟩
    rwa [hy₂] at this
  have ha₃ : T.Adj v y₃ := by
    have := hT.edge_mem ⟨C', ⟨S₃, hS₃m⟩⟩
    rwa [hy₃] at this
  have hyy : y₂ ≠ y₃ := by
    rintro rfl
    have := hT.edge_injective_of_center hv' (k₁ := ⟨C', ⟨S₂, hS₂m⟩⟩) (k₂ := ⟨C', ⟨S₃, hS₃m⟩⟩) rfl rfl (hy₂.trans hy₃.symm)
    exact hne₂₃ (by simpa using this)
  have hfar : ∀ {S : C'.supp → Bool} (hS : S ∈ restrictRows C'.supp M) {y : W}, edge ⟨C', ⟨S, hS⟩⟩ = s(v, y) → ∀ {r} (hr : r ∈ M), C'.supp.domRestrict r = S →
      SameSide T s(v, y) y (φ ⟨r, hr⟩) := by
    intro S hS y hy r hr hrS
    refine (SempleSteel2003.reachable_deleteEdges_or hT.isTree.connected v y _).resolve_left fun h => hv' ⟨C', ⟨S, hS⟩⟩ rfl ⟨r, hr⟩ (decide_eq_true hrS) ?_
    rw [hy]
    exact h.symm
  have hb := sameSide_left_of_sameSide hT.isTree ha₂ ha₃ hyy (hfar hS₂m hy₂ hr₂ hr₂S) (hfar hS₃m hy₃ hr₃ hr₃S) hss
  exact ⟨⟨r₂, hr₂⟩, ht₂, hb.symm⟩

omit [Finite ι] in
/-- A site's state, at the centre of its component, is compatible with a character having that centre on its 1-side (line 416): some row has both. -/
theorem IsTBar.exists_row_of_center [Finite W] (hT : IsTBar M T φ edge) {C : (incompatGraph M).ConnectedComponent} (hnt : C.supp.Nontrivial) {v : W}
    (hv : ∀ k : SuperChar M, k.1 = C → v ∈ edge k) (hv' : ∀ k : SuperChar M, k.1 = C → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v)
    {k' : SuperChar M} (hk' : OnOneSide T φ edge k' v) {i : ι} (hi : i ∈ C.supp) (a : Bool) : ∃ x : M, x.1 i = a ∧ charValue k' x = true := by
  obtain ⟨j, hj, hij⟩ : ∃ j ∈ C.supp, j ≠ i := by
    obtain ⟨p, hp, q, hq, hpq⟩ := hnt
    by_cases hpi : p = i
    · exact ⟨q, hq, fun h => hpq (hpi.trans h.symm)⟩
    · exact ⟨p, hp, hpi⟩
  have hreach : (incompatGraph M).Reachable i j := SimpleGraph.ConnectedComponent.eq.1 (hi.trans (Eq.symm hj))
  obtain ⟨i₂, hi₂⟩ := exists_adj_of_reachable hreach (Ne.symm hij)
  have hi₂C : i₂ ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hi ⊢
    rw [← hi]
    exact SimpleGraph.ConnectedComponent.eq.2 hi₂.reachable.symm
  obtain ⟨r₀, hr₀, h₀a, h₀b⟩ := hi₂ a false
  obtain ⟨r₁, hr₁, h₁a, h₁b⟩ := hi₂ a true
  have hS : ∀ {r : ι → Bool}, r ∈ M → C.supp.domRestrict r ∈ restrictRows C.supp M := fun hr => mem_restrictRows.2 ⟨_, hr, rfl⟩
  have hkey : ∀ {r : ι → Bool} (hr : r ∈ M), r i = a → edge ⟨C, ⟨_, hS hr⟩⟩ ≠ edge k' → ∃ x : M, x.1 i = a ∧ charValue k' x = true := by
    intro r hr hra hne
    obtain ⟨y, hy⟩ := hv ⟨C, ⟨_, hS hr⟩⟩ rfl
    have hadj : T.Adj v y := by
      have := hT.edge_mem ⟨C, ⟨_, hS hr⟩⟩
      rwa [hy] at this
    have hvy : SameSide T (edge k') v y := (SempleSteel2003.deleteEdges_adj_of_ne hadj (by rw [← hy]; exact hne)).reachable
    obtain ⟨x, hx₁, hx₂⟩ := exists_label_sameSide hT.isTree hT.labelled (edge ⟨C, ⟨_, hS hr⟩⟩) (edge k') y
    have hfar : SameSide T (edge ⟨C, ⟨_, hS hr⟩⟩) y (φ ⟨r, hr⟩) := by
      rw [hy]
      refine (SempleSteel2003.reachable_deleteEdges_or hT.isTree.connected v y _).resolve_left fun h => hv' ⟨C, ⟨_, hS hr⟩⟩ rfl ⟨r, hr⟩ (decide_eq_true rfl) ?_
      rw [hy]
      exact h.symm
    have h₁ : charValue (⟨C, ⟨_, hS hr⟩⟩ : SuperChar M) x = true :=
      ((hT.split ⟨C, ⟨_, hS hr⟩⟩ ⟨r, hr⟩ x).2 (hfar.symm.trans hx₁)).symm.trans (decide_eq_true rfl)
    have h₂ : C.supp.domRestrict x.1 = C.supp.domRestrict r := by simpa [charValue] using h₁
    refine ⟨x, (congrFun h₂ ⟨i, hi⟩).trans hra, ?_⟩
    obtain ⟨r', hr', hrv'⟩ := hk'
    exact ((hT.split k' r' x).2 (hrv'.trans (hvy.trans hx₂))).symm.trans hr'
  have hne₀₁ : (⟨C, ⟨_, hS hr₀⟩⟩ : SuperChar M) ≠ ⟨C, ⟨_, hS hr₁⟩⟩ := by
    intro h
    have h' : C.supp.domRestrict r₀ = C.supp.domRestrict r₁ := by simpa using h
    have := congrFun h' ⟨i₂, hi₂C⟩
    change r₀ i₂ = r₁ i₂ at this
    rw [h₀b, h₁b] at this
    exact absurd this (by simp)
  by_cases he : edge ⟨C, ⟨_, hS hr₀⟩⟩ = edge k'
  · refine hkey hr₁ h₁a fun he' => hne₀₁ ?_
    exact hT.edge_injective_of_center hv' rfl rfl (he.trans he'.symm)
  · exact hkey hr₀ h₀a he



omit [LinearOrder ι] [Finite ι] in
/-- If no two sites in different components of `G(M)` have a row missing the sequence `S`, then `S` doesn't merge components. -/
theorem reachable_conflictGraph_of_row {M : Finset (ι → Bool)} {S : ι → Bool} (h : ∀ i j, ¬ (incompatGraph M).Reachable i j → ∃ r ∈ M, r i = S i ∧ r j = S j) (i j : ι) :
    (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j := by
  constructor
  · intro hr
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail a b _ hadj ih =>
      refine ih.trans ?_
      by_contra hnr
      obtain ⟨r, hr, h₁, h₂⟩ := h a b hnr
      refine hnr (SimpleGraph.Adj.reachable (fun x y => ?_))
      by_cases hxy : x = S a ∧ y = S b
      · exact ⟨r, hr, h₁.trans hxy.1.symm, h₂.trans hxy.2.symm⟩
      · exact hadj x y (by tauto)
  · have hle : incompatGraph M ≤ conflictGraph S M := fun a b (hab : Incompatible M a b) x y _ => hab x y
    exact fun h' => h'.mono hle

omit [LinearOrder ι] [Finite ι] in
/-- The sites in two non-trivial components, with `S` not dominant in either, conflict. So if `S` doesn't merge components, it's dominant in one of them (line 576). -/
theorem exists_dominant_of_reachable {M : Finset (ι → Bool)} {S : ι → Bool} (hS : ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j)
    {C C' : (incompatGraph M).ConnectedComponent} (hne : C ≠ C') (hnt : C.supp.Nontrivial) (hnt' : C'.supp.Nontrivial) {d : C.supp → Bool} {d' : C'.supp → Bool}
    (hdom : IsDominantFor M C.supp C'.supp d d') : C.supp.domRestrict S = d ∨ C'.supp.domRestrict S = d' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn₁, hn₂⟩ := hcon
  have hex₁ : ∃ i : C.supp, S i ≠ d i := by
    by_contra h
    push Not at h
    exact hn₁ (funext h)
  have hex₂ : ∃ j : C'.supp, S j ≠ d' j := by
    by_contra h
    push Not at h
    exact hn₂ (funext h)
  obtain ⟨i, hi⟩ := hex₁
  obtain ⟨j, hj⟩ := hex₂
  have hcard : ∀ x y : Bool, ({p | p ≠ (x, y)} : Set (Bool × Bool)).ncard = 3 := by
    intro x y
    have h : ({p | p ≠ (x, y)} : Set (Bool × Bool)) = ↑((Finset.univ : Finset (Bool × Bool)).erase (x, y)) := by
      ext p
      simp
    rw [h, Set.ncard_coe_finset]
    cases x <;> cases y <;> decide
  have hsub : (fun r : ι → Bool => (r i.1, r j.1)) '' (M : Set (ι → Bool)) ⊆ {p | p ≠ (S i.1, S j.1)} := by
    rintro _ ⟨r, hr, rfl⟩ h
    have h₁ : r i.1 = S i.1 := congrArg Prod.fst h
    have h₂ : r j.1 = S j.1 := congrArg Prod.snd h
    rcases hdom i j r hr with h₃ | h₃
    · exact hi (h₁.symm.trans h₃)
    · exact hj (h₂.symm.trans h₃)
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_pairs_eq_three M hne hnt hnt' i.2 j.2]) (Set.toFinite _)
  have hconf : Conflict S M i.1 j.1 := by
    intro a b hab
    have hm : (a, b) ∈ (fun r : ι → Bool => (r i.1, r j.1)) '' (M : Set (ι → Bool)) := by
      rw [heq]
      intro h
      have h₁ : a = S i.1 := congrArg Prod.fst h
      have h₂ : b = S j.1 := congrArg Prod.snd h
      rcases hab with hab | hab
      · exact hab h₁
      · exact hab h₂
    obtain ⟨r, hr, hre⟩ := hm
    exact ⟨r, hr, congrArg Prod.fst hre, congrArg Prod.snd hre⟩
  have hreach : (incompatGraph M).Reachable i.1 j.1 := (hS _ _).1 (SimpleGraph.Adj.reachable hconf)
  apply hne
  rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 i.2, ← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 j.2]
  exact SimpleGraph.ConnectedComponent.eq.2 hreach

omit [LinearOrder ι] [Finite ι] in
/-- Three components: if `C₁` and `C₂` are in two branches at `C`, then `C` and `C₂` are in one branch at `C₁`. On rows: else the sites of `C₂` have a constant column. -/
theorem dominant_eq_of_ne {M : Finset (ι → Bool)} (hC : NoConstantColumn M) {C C₁ C₂ : (incompatGraph M).ConnectedComponent} (h₀₁ : C ≠ C₁) (h₀₂ : C ≠ C₂) (h₁₂ : C₁ ≠ C₂)
    (hnt₁ : C₁.supp.Nontrivial) {d₁ : C.supp → Bool} {e₁ : C₁.supp → Bool} (h₁ : IsDominantFor M C.supp C₁.supp d₁ e₁) {d₂ : C.supp → Bool} {g₂ : C₂.supp → Bool}
    (h₂ : IsDominantFor M C.supp C₂.supp d₂ g₂) {e₂ : C₁.supp → Bool} {h₃ : C₂.supp → Bool} (hh₃ : IsDominantFor M C₁.supp C₂.supp e₂ h₃) (hne : d₁ ≠ d₂) : e₁ = e₂ := by
  by_contra he
  have h4 := four_le_card_restrictRows hnt₁
  have h2 : 0 < (((restrictRows C₁.supp M).erase e₁).erase e₂).card := by
    have h₅ := Finset.pred_card_le_card_erase (s := restrictRows C₁.supp M) (a := e₁)
    have h₆ := Finset.pred_card_le_card_erase (s := (restrictRows C₁.supp M).erase e₁) (a := e₂)
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.1 h2
  obtain ⟨hx₂, hx₁'⟩ := Finset.mem_erase.1 hx
  obtain ⟨hx₁, hxm⟩ := Finset.mem_erase.1 hx₁'
  obtain ⟨r, hr, hrx⟩ := mem_restrictRows.1 hxm
  have hrC : C.supp.domRestrict r = d₁ := (corollary1 M h₀₁ h₁ hr).resolve_right fun h => hx₁ (hrx.symm.trans h)
  have hrg : C₂.supp.domRestrict r = g₂ := (corollary1 M h₀₂ h₂ hr).resolve_left fun h => hne (hrC.symm.trans h)
  have hrh : C₂.supp.domRestrict r = h₃ := (corollary1 M h₁₂ hh₃ hr).resolve_left fun h => hx₂ (hrx.symm.trans h)
  have hgh : g₂ = h₃ := hrg.symm.trans hrh
  have hall : ∀ r ∈ M, C₂.supp.domRestrict r = g₂ := by
    intro r hr
    by_cases hre : C₁.supp.domRestrict r = e₁
    · rw [hgh]
      exact (corollary1 M h₁₂ hh₃ hr).resolve_left fun h => he (hre.symm.trans h)
    · have hrC' : C.supp.domRestrict r = d₁ := (corollary1 M h₀₁ h₁ hr).resolve_right hre
      exact (corollary1 M h₀₂ h₂ hr).resolve_left fun h => hne (hrC'.symm.trans h)
  obtain ⟨i, hi⟩ := C₂.nonempty_supp
  obtain ⟨r₁, hr₁, r₂, hr₂, hne'⟩ := hC i
  exact hne' ((congrFun (hall r₁ hr₁) ⟨i, hi⟩).trans (congrFun (hall r₂ hr₂) ⟨i, hi⟩).symm)

omit [LinearOrder ι] in
/-- **Where the root is, if it doesn't merge components.** There's a non-trivial component `C*` such that `S` has, on each other non-trivial component, the dominant sequence with respect to `C*`: the centre of `C*` is as good a root as `S`. -/
theorem exists_sink {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (hS : ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j)
    (hnon : ∃ C : (incompatGraph M).ConnectedComponent, C.supp.Nontrivial) :
    ∃ C₀ : (incompatGraph M).ConnectedComponent, C₀.supp.Nontrivial ∧ ∀ C : (incompatGraph M).ConnectedComponent, C.supp.Nontrivial → C ≠ C₀ →
      ∃ d d', IsDominantFor M C.supp C₀.supp d d' ∧ C.supp.domRestrict S = d := by
  set Arrow : (incompatGraph M).ConnectedComponent → (incompatGraph M).ConnectedComponent → Prop := fun C C' =>
    ∃ d d', IsDominantFor M C.supp C'.supp d d' ∧ C.supp.domRestrict S = d with hArrow
  have hswap : ∀ {C C' : (incompatGraph M).ConnectedComponent} {d : C.supp → Bool} {d' : C'.supp → Bool}, IsDominantFor M C.supp C'.supp d d' → IsDominantFor M C'.supp C.supp d' d :=
    fun h i' i r hr => (h i i' r hr).symm
  have hor : ∀ {C C' : (incompatGraph M).ConnectedComponent}, C ≠ C' → C.supp.Nontrivial → C'.supp.Nontrivial → Arrow C C' ∨ Arrow C' C := by
    intro C C' hne hnt hnt'
    obtain ⟨d, d', hdom⟩ := exists_isDominantFor M hne
    rcases exists_dominant_of_reachable hS hne hnt hnt' hdom with h | h
    · exact Or.inl ⟨d, d', hdom, h⟩
    · exact Or.inr ⟨d', d, hswap hdom, h⟩
  have : Nonempty {C : (incompatGraph M).ConnectedComponent // C.supp.Nontrivial} := by
    obtain ⟨C, hC'⟩ := hnon
    exact ⟨⟨C, hC'⟩⟩
  have : Finite (incompatGraph M).ConnectedComponent := Quot.finite _
  obtain ⟨⟨C₀, hC₀⟩, hmax⟩ := Finite.exists_max (fun C : {C : (incompatGraph M).ConnectedComponent // C.supp.Nontrivial} =>
    Set.ncard {C' : (incompatGraph M).ConnectedComponent | C'.supp.Nontrivial ∧ (C' = C.1 ∨ Arrow C' C.1)})
  refine ⟨C₀, hC₀, fun C₁ hC₁ hne₁ => ?_⟩
  by_contra hnot
  have hlt : Set.ncard {C' : (incompatGraph M).ConnectedComponent | C'.supp.Nontrivial ∧ (C' = C₀ ∨ Arrow C' C₀)} <
      Set.ncard {C' : (incompatGraph M).ConnectedComponent | C'.supp.Nontrivial ∧ (C' = C₁ ∨ Arrow C' C₁)} := by
    refine Set.ncard_lt_ncard ⟨?_, fun hsub => ?_⟩ (Set.toFinite _)
    · rintro C' ⟨hnt', rfl | ha⟩
      · refine ⟨hC₀, Or.inr ((hor (Ne.symm hne₁) hC₀ hC₁).resolve_right hnot)⟩
      · refine ⟨hnt', ?_⟩
        by_cases hC'₁ : C' = C₁
        · exact Or.inl hC'₁
        · right
          by_contra hna
          by_cases hC'₀ : C' = C₀
          · subst hC'₀
            exact hna ((hor (Ne.symm hne₁) hC₀ hC₁).resolve_right hnot)
          obtain ⟨e₀, d₀, hdom₀, hS₀⟩ := (hor hC'₁ hnt' hC₁).resolve_left hna
          obtain ⟨d₂, g₂, hdom₂, hS₂⟩ := ha
          obtain ⟨d₁, e₁, hdom₁⟩ := exists_isDominantFor M hC'₁
          obtain ⟨e₂, h₂, hdom₃⟩ := exists_isDominantFor M hne₁
          have huniq := isDominantFor_unique hC (Ne.symm hC'₁) (Or.inl hC₁) hdom₀ (hswap hdom₁)
          have hne' : d₁ ≠ d₂ := by
            intro hdd
            apply hna
            refine ⟨d₁, e₁, hdom₁, ?_⟩
            rw [hS₂, hdd]
          have hee := dominant_eq_of_ne hC hC'₁ hC'₀ hne₁ hC₁ hdom₁ hdom₂ hdom₃ hne'
          apply hnot
          refine ⟨e₂, h₂, hdom₃, ?_⟩
          rw [hS₀, huniq.1, hee]
    · exact (hsub ⟨hC₁, Or.inl rfl⟩ : _ ∧ _).2.elim hne₁ hnot
  exact absurd (hmax ⟨C₁, hC₁⟩) (not_le.2 hlt)

omit [Finite ι] in
theorem rootCost_eq_of_onOneSide [Finite W] (c : Crossover) (hT : IsTBar M T φ edge) {C : (incompatGraph M).ConnectedComponent} {S₀ : C.supp → Bool} (hS₀ : S₀ ∈ restrictRows C.supp M) {v : W}
    (h : OnOneSide T φ edge (⟨C, ⟨S₀, hS₀⟩⟩ : SuperChar M) v) : rootCost c M T φ edge v C = RS c S₀ (restrictRows C.supp M) := by
  have hex : ∃ (S₀ : C.supp → Bool) (hS₀ : S₀ ∈ restrictRows C.supp M) (r : M),
      charValue (⟨C, ⟨S₀, hS₀⟩⟩ : SuperChar M) r = true ∧ SameSide T (edge ⟨C, ⟨S₀, hS₀⟩⟩) (φ r) v := ⟨S₀, hS₀, h⟩
  rw [rootCost, dite_eq_left hex]
  obtain ⟨hmem, hr⟩ := hex.choose_spec
  have heq := hT.eq_of_onOneSide (k := ⟨C, ⟨hex.choose, hmem⟩⟩) (k' := ⟨C, ⟨S₀, hS₀⟩⟩) rfl hr h
  have hS : hex.choose = S₀ := by simpa using heq
  rw [hS]

omit [Finite ι] in
theorem rootCost_eq_of_not (c : Crossover) {C : (incompatGraph M).ConnectedComponent} {v : W} (h : ∀ k : SuperChar M, k.1 = C → ¬ OnOneSide T φ edge k v) :
    rootCost c M T φ edge v C = R c (restrictRows C.supp M) := by
  have hex : ¬ ∃ (S₀ : C.supp → Bool) (hS₀ : S₀ ∈ restrictRows C.supp M) (r : M),
      charValue (⟨C, ⟨S₀, hS₀⟩⟩ : SuperChar M) r = true ∧ SameSide T (edge ⟨C, ⟨S₀, hS₀⟩⟩) (φ r) v := by
    rintro ⟨S₀, hS₀, hr⟩
    exact h ⟨C, ⟨S₀, hS₀⟩⟩ rfl hr
  rw [rootCost, dite_eq_right hex]

/-- The cost of a trivial component is zero, wherever the root is. -/
theorem rootCost_eq_zero (c : Crossover) (hM : M.Nonempty) (hC : NoConstantColumn M) {C : (incompatGraph M).ConnectedComponent} (hnt : ¬ C.supp.Nontrivial) (v : W) :
    rootCost c M T φ edge v C = 0 := by
  unfold rootCost
  split
  · exact RS_eq_zero_of_not_nontrivial c M hM hC hnt _
  · have hS₀ : ∃ S₀ : C.supp → Bool, True := ⟨fun _ => false, trivial⟩
    obtain ⟨S₀, -⟩ := hS₀
    have hle : R c (restrictRows C.supp M) ≤ RS c S₀ (restrictRows C.supp M) := by
      refine R_le_RS c S₀ ?_
      obtain ⟨r, hr⟩ := hM
      exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
    rw [RS_eq_zero_of_not_nontrivial c M hM hC hnt S₀] at hle
    exact Nat.le_zero.1 hle

/-- **The root at a node of `T̄` is a sequence**: `S` is the super-character of each component on whose 1-side the node is, and at the centre, the ancestral sequence of an optimal network for `M(C)`. Such an `S` doesn't merge components. -/
theorem exists_root_of_node (c : Crossover) (hM : M.Nonempty) (hC : NoConstantColumn M) [Finite W] (hT : IsTBar M T φ edge) (v : W) :
    ∃ S : ι → Bool, (∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) ∧
      ∀ C : (incompatGraph M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) = rootCost c M T φ edge v C := by
  have hL : ∀ C : (incompatGraph M).ConnectedComponent, (restrictRows C.supp M).Nonempty := by
    intro C
    obtain ⟨r, hr⟩ := hM
    exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
  have hpick : ∀ C : (incompatGraph M).ConnectedComponent, ∃ g : C.supp → Bool, RS c g (restrictRows C.supp M) = rootCost c M T φ edge v C ∧
      ∀ k : SuperChar M, k.1 = C → OnOneSide T φ edge k v → ∃ hg : g ∈ restrictRows C.supp M, OnOneSide T φ edge (⟨C, ⟨g, hg⟩⟩ : SuperChar M) v := by
    intro C
    by_cases hk : ∃ k : SuperChar M, k.1 = C ∧ OnOneSide T φ edge k v
    · obtain ⟨⟨c', S₀, hS₀⟩, hc', hon⟩ := hk
      obtain rfl : c' = C := hc'
      refine ⟨S₀, (rootCost_eq_of_onOneSide c hT hS₀ hon).symm, fun _ _ _ => ⟨hS₀, hon⟩⟩
    · push Not at hk
      obtain ⟨a, b, N, h₁, h₂, h₃⟩ := Nat.sInf_mem (recombSet_nonempty c (hL C))
      refine ⟨N.ancestral, ?_, fun k hk₁ hk₂ => absurd hk₂ (hk k hk₁)⟩
      rw [rootCost_eq_of_not c hk]
      refine le_antisymm ?_ (R_le_RS c _ (hL C))
      have : RS c N.ancestral (restrictRows C.supp M) ≤ N.recombCount := Nat.sInf_le ⟨a, b, N, h₁, h₂, rfl, rfl⟩
      exact this.trans h₃.le
  choose g hg hg' using hpick
  set S : ι → Bool := fun i => g ((incompatGraph M).connectedComponentMk i) ⟨i, rfl⟩ with hSdef
  have hres : ∀ C : (incompatGraph M).ConnectedComponent, C.supp.domRestrict S = g C := by
    intro C
    funext ⟨i, hi⟩
    obtain rfl : (incompatGraph M).connectedComponentMk i = C := hi
    rfl
  have hrow : ∀ i j, ¬ (incompatGraph M).Reachable i j → ∃ r ∈ M, r i = S i ∧ r j = S j := by
    intro i j hnr
    set C := (incompatGraph M).connectedComponentMk i with hCi
    set C' := (incompatGraph M).connectedComponentMk j with hCj
    have hne : C ≠ C' := fun h => hnr (SimpleGraph.ConnectedComponent.eq.1 h)
    have hval : ∀ {C₁ : (incompatGraph M).ConnectedComponent} {l : ι} (hl : l ∈ C₁.supp) {x : ι → Bool} (hgm : g C₁ ∈ restrictRows C₁.supp M),
        charValue (⟨C₁, ⟨g C₁, hgm⟩⟩ : SuperChar M) x = true → x l = S l := by
      intro C₁ l hl x hgm hx
      have h₁ : C₁.supp.domRestrict x = g C₁ := by simpa [charValue] using hx
      have h₂ := (congrFun h₁ ⟨l, hl⟩).trans (congrFun (hres C₁) ⟨l, hl⟩).symm
      exact h₂
    by_cases hk : ∃ k : SuperChar M, k.1 = C ∧ OnOneSide T φ edge k v
    · obtain ⟨k, hk₁, hk₂⟩ := hk
      obtain ⟨hgm, hon⟩ := hg' C k hk₁ hk₂
      by_cases hk' : ∃ k : SuperChar M, k.1 = C' ∧ OnOneSide T φ edge k v
      · obtain ⟨k', hk'₁, hk'₂⟩ := hk'
        obtain ⟨hgm', hon'⟩ := hg' C' k' hk'₁ hk'₂
        obtain ⟨x, hx, hx'⟩ := hT.exists_row_of_onOneSide hon hon'
        exact ⟨x.1, x.2, hval rfl hgm hx, hval rfl hgm' hx'⟩
      · push Not at hk'
        have hnt' : C'.supp.Nontrivial := by
          by_contra hnt'
          obtain ⟨k₁, hk₁', hk₂'⟩ := hT.exists_onOneSide_of_trivial hC hnt' v
          exact hk' k₁ hk₁' hk₂'
        obtain ⟨v₀, hv₀, hv₀', -⟩ := lemma4 hT C'
        have hnot : ∀ k : SuperChar M, k.1 = C' → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v :=
          fun k hk₁ r hr hs => hk' k hk₁ ⟨r, hr, hs⟩
        have hvv := hT.eq_center hnt' hv₀ (hv₀' hnt') hnot
        obtain ⟨x, hxj, hx⟩ := hT.exists_row_of_center hnt' (hvv ▸ hv₀) hnot hon (i := j) rfl (S j)
        exact ⟨x.1, x.2, hval rfl hgm hx, hxj⟩
    · push Not at hk
      have hnt : C.supp.Nontrivial := by
        by_contra hnt
        obtain ⟨k₁, hk₁', hk₂'⟩ := hT.exists_onOneSide_of_trivial hC hnt v
        exact hk k₁ hk₁' hk₂'
      obtain ⟨v₀, hv₀, hv₀', -⟩ := lemma4 hT C
      have hnot : ∀ k : SuperChar M, k.1 = C → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v :=
        fun k hk₁ r hr hs => hk k hk₁ ⟨r, hr, hs⟩
      have hvv := hT.eq_center hnt hv₀ (hv₀' hnt) hnot
      have hvC : ∀ k : SuperChar M, k.1 = C → v ∈ edge k := hvv ▸ hv₀
      by_cases hk' : ∃ k : SuperChar M, k.1 = C' ∧ OnOneSide T φ edge k v
      · obtain ⟨k', hk'₁, hk'₂⟩ := hk'
        obtain ⟨hgm', hon'⟩ := hg' C' k' hk'₁ hk'₂
        obtain ⟨x, hxi, hx⟩ := hT.exists_row_of_center hnt hvC hnot hon' (i := i) rfl (S i)
        exact ⟨x.1, x.2, hxi, hval rfl hgm' hx⟩
      · push Not at hk'
        exfalso
        have hnt' : C'.supp.Nontrivial := by
          by_contra hnt'
          obtain ⟨k₁, hk₁', hk₂'⟩ := hT.exists_onOneSide_of_trivial hC hnt' v
          exact hk' k₁ hk₁' hk₂'
        obtain ⟨v₁, hv₁, hv₁', -⟩ := lemma4 hT C'
        have hnot' : ∀ k : SuperChar M, k.1 = C' → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v :=
          fun k hk₁ r hr hs => hk' k hk₁ ⟨r, hr, hs⟩
        have hvv' := hT.eq_center hnt' hv₁ (hv₁' hnt') hnot'
        exact hT.center_ne hne hnt hvC hnot (hvv' ▸ hv₁) hnot'
  exact ⟨S, reachable_conflictGraph_of_row hrow, fun C => by rw [hres, hg]⟩

/-- **The root at any node of `T̄`** gives a fully decomposed network with `Σ rootCost` recombination nodes, by Theorem 3, since the sequence of `exists_root_of_node` doesn't merge components. -/
theorem F_le_sum_rootCost (c : Crossover) (hM : M.Nonempty) (hC : NoConstantColumn M) [Finite W] (hT : IsTBar M T φ edge) (v : W) :
    F c M ≤ ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C := by
  obtain ⟨S, hreach, hS⟩ := exists_root_of_node c hM hC hT v
  obtain ⟨a, b, N, h₁, h₂, -, h₄, h₅⟩ := theorem3 c M S hM hC
  have hF : F c M ≤ N.recombCount := Nat.sInf_le ⟨a, b, N, h₁, h₂, h₄.of_reachable_iff hreach, rfl⟩
  refine hF.trans (le_of_eq ?_)
  rw [h₅, finsum_connectedComponent_congr hreach (fun s => RS c (s.domRestrict S) (restrictRows s M))]
  exact finsum_congr hS

/-- **Line 418's second fact** (`g:root_interior`). "Placing the root of `T̄` at a leaf or on the interior of an edge will not reduce the number of required recombinations." A root anywhere on `T̄` is a sequence `S` that doesn't merge components, and it costs `Σ R_{S(C)}(M(C))`. This is no less than the cost of an interior node. If there's a non-trivial
component, `exists_sink` finds a component `C*` such that `S` is dominant towards `C*` in each other non-trivial component. So the centre of `C*` costs no more than `S`: it's on the 1-side of the super-character of `S` in each other component (`IsTBar.onOneSide_of_isDominantFor`), and for `C*` itself the cost is `R(M(C*)) ≤ R_{S(C*)}(M(C*))`. If there's none, each cost is zero.
`T̄` has an interior node unless `M` has at most two rows. -/
theorem exists_interior_sum_rootCost_le (c : Crossover) (hM : M.Nonempty) (hC : NoConstantColumn M) [Finite W] (hT : IsTBar M T φ edge) (hint : ∃ v, 2 ≤ (T.neighborSet v).ncard) {S : ι → Bool}
    (hS : ∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) :
    ∃ v, 2 ≤ (T.neighborSet v).ncard ∧ ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C ≤
      ∑ᶠ C : (incompatGraph M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  have : Fintype (incompatGraph M).ConnectedComponent := Fintype.ofFinite _
  by_cases hnon : ∃ C : (incompatGraph M).ConnectedComponent, C.supp.Nontrivial
  · obtain ⟨C₀, hC₀, hsink⟩ := exists_sink hC hS hnon
    obtain ⟨v, hv, hv', -⟩ := lemma4 hT C₀
    refine ⟨v, hT.two_le_ncard_center hC₀ hv (hv' hC₀), ?_⟩
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    refine Finset.sum_le_sum fun C _ => ?_
    by_cases hnt : C.supp.Nontrivial
    · by_cases hCC : C = C₀
      · subst hCC
        rw [rootCost_eq_of_not c fun k hk ⟨r, hr, hs⟩ => hv' hC₀ k hk r hr hs]
        refine R_le_RS c _ ?_
        obtain ⟨r, hr⟩ := hM
        exact ⟨_, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩
      · obtain ⟨d, d', hdom, hSd⟩ := hsink C hnt hCC
        have hd := dominant_mem_restrictRows hC hCC hdom
        rw [rootCost_eq_of_onOneSide c hT hd (hT.onOneSide_of_isDominantFor hCC hC₀ hdom hv (hv' hC₀) hd), hSd]
    · rw [rootCost_eq_zero c hM hC hnt]
      exact Nat.zero_le _
  · push Not at hnon
    obtain ⟨v, hv⟩ := hint
    refine ⟨v, hv, ?_⟩
    rw [finsum_eq_sum_of_fintype, Finset.sum_eq_zero fun C _ => rootCost_eq_zero c hM hC (Set.not_nontrivial_iff.2 (hnon C)) v]
    exact Nat.zero_le _

/-- Line 418's second fact, for a root at a node of `T̄`, such as a leaf: an interior node costs no more. -/
theorem exists_interior_sum_rootCost_le_of_node (c : Crossover) (hM : M.Nonempty) (hC : NoConstantColumn M) [Finite W] (hT : IsTBar M T φ edge) (hint : ∃ v, 2 ≤ (T.neighborSet v).ncard) (v₀ : W) :
    ∃ v, 2 ≤ (T.neighborSet v).ncard ∧ ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C ≤
      ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v₀ C := by
  obtain ⟨S, hreach, hS⟩ := exists_root_of_node c hM hC hT v₀
  obtain ⟨v, hv, hle⟩ := exists_interior_sum_rootCost_le c hM hC hT hint hreach
  exact ⟨v, hv, hle.trans_eq (finsum_congr hS)⟩

/-- **Lines 416, 418** (`g:compute_F`). "Even if `M` is not min-decomposable or min-1 decomposable, the procedure above will correctly compute
`F(M)` or `F¹(M)`": the procedure tries each interior node `v` of `T̄` as the root, solves a rooted problem for each component except
the one with centre `v`, and an unrooted one for that. The correctness is said to follow "from Theorem 4 and the fact that placing the root of
`T̄` at a leaf or on the interior of an edge will not reduce the number of required recombinations" (line 418). When `T̄` has no interior node, the set is empty and `sInf` is `0`, which is right: there's no non-trivial
component.

Departure from the paper: its route reads the root's place in `T̄` off a fully decomposed network, by Theorem 4, which is false as printed (`theorem4_false_top`); and the corrected form, `theorem4_iff`, applies only to networks with `IsTreeNormalStructural` and the degree condition. An optimal fully decomposed network needn't have them. Lean starts from `F_eq_sInf_roots`,
so from the ancestral sequence `S` of an optimal fully decomposed network, which doesn't merge components. The paper's second fact, that moving the root to an interior node doesn't raise the count, is `exists_interior_sum_rootCost_le`, whose proof uses `exists_sink`. The other direction is `F_le_sum_rootCost`, the paper's construction. So Theorem 4 isn't used. -/
theorem F_eq_sInf_interior (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) [Finite W]
    {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W} (hT : IsTBar M T φ edge) :
    F c M = sInf {k | ∃ v, 2 ≤ (T.neighborSet v).ncard ∧
      k = ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C} := by
  have hle := F_le_sum_rootCost (T := T) (φ := φ) (edge := edge) c hM hC hT
  have : Fintype (incompatGraph M).ConnectedComponent := Fintype.ofFinite _
  by_cases hnon : ∃ C : (incompatGraph M).ConnectedComponent, C.supp.Nontrivial
  · -- the ancestral sequence of an optimal fully decomposed network
    obtain ⟨a, b, N, h₁, h₂, h₃⟩ := theorem1 c M hM hC
    have hmem := Nat.sInf_mem (s := {k | ∃ S : ι → Bool, (∀ i j, (conflictGraph S M).Reachable i j ↔ (incompatGraph M).Reachable i j) ∧
      k = ∑ᶠ C : (conflictGraph S M).ConnectedComponent, RS c (C.supp.domRestrict S) (restrictRows C.supp M)})
      ⟨_, N.ancestral, reachable_conflictGraph_iff h₂ h₃, rfl⟩
    rw [← F_eq_sInf_roots c M hM hC] at hmem
    obtain ⟨S, hS, hF⟩ := hmem
    rw [finsum_connectedComponent_congr hS (fun s => RS c (s.domRestrict S) (restrictRows s M))] at hF
    obtain ⟨C₀, hC₀⟩ := hnon
    obtain ⟨v₀, hv₀, hv₀', -⟩ := lemma4 hT C₀
    obtain ⟨v, hint, hsum⟩ := exists_interior_sum_rootCost_le c hM hC hT ⟨v₀, hT.two_le_ncard_center hC₀ hv₀ (hv₀' hC₀)⟩ hS
    rw [← hF] at hsum
    refine le_antisymm (le_csInf ⟨_, v, hint, rfl⟩ ?_) (csInf_le_of_le (OrderBot.bddBelow _) ⟨v, hint, rfl⟩ hsum)
    rintro _ ⟨v', -, rfl⟩
    exact hle v'
  · push Not at hnon
    have hzero : ∀ v, ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C = 0 := by
      intro v
      rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_eq_zero fun C _ => rootCost_eq_zero c hM hC (Set.not_nontrivial_iff.2 (hnon C)) v
    obtain ⟨r₀, hr₀⟩ := hM
    have hF : F c M = 0 := Nat.le_zero.1 ((hle (φ ⟨r₀, hr₀⟩)).trans (hzero _).le)
    rw [hF]
    by_cases hne : {k | ∃ v, 2 ≤ (T.neighborSet v).ncard ∧ k = ∑ᶠ C : (incompatGraph M).ConnectedComponent, rootCost c M T φ edge v C}.Nonempty
    · obtain ⟨v, -, hv⟩ := Nat.sInf_mem hne
      rw [hv, hzero]
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Nat.sInf_empty]

end ComputeF

end Gusfield2007
