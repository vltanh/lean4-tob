module

public import Gusfield2007.Structure
public import Gusfield2007.TreeContract
public import External.SempleSteel2003.SplitsEquivalence
public import External.Gusfield1991.PerfectPhylogeny

/-!
# Gusfield et al. 2007, Sections 3.2 and 3.3: super-characters, the matrix `B`, the tree `T̄`

Lemma 3, the existence and uniqueness of `T̄`, Lemma 4.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

variable {ι : Type*}

theorem charValue_mk_iff {M : Finset (ι → Bool)} {c : (incompatGraph M).ConnectedComponent}
    {S : {S // S ∈ restrictRows c.supp M}} {r : ι → Bool} :
    charValue (⟨c, S⟩ : SuperChar M) r = true ↔ c.supp.domRestrict r = S.1 := by
  simp [charValue]

theorem domRestrict_ne_of_charValue_eq_false {M : Finset (ι → Bool)} {c : (incompatGraph M).ConnectedComponent}
    {S : {S // S ∈ restrictRows c.supp M}} {r : ι → Bool} (h : charValue (⟨c, S⟩ : SuperChar M) r = false) :
    c.supp.domRestrict r ≠ S.1 := fun h' => by
  rw [charValue_mk_iff.2 h'] at h
  exact absurd h (by simp)

/-- **Line 283** (`g:char_unique`). "Every row in `B` has value 1 in exactly one column of `B(C)`". -/
theorem existsUnique_charValue_eq_true {M : Finset (ι → Bool)} (c : (incompatGraph M).ConnectedComponent) {r : ι → Bool}
    (hr : r ∈ M) : ∃! k : SuperChar M, k.1 = c ∧ charValue k r = true := by
  refine ⟨⟨c, ⟨c.supp.domRestrict r, mem_restrictRows.2 ⟨r, hr, rfl⟩⟩⟩, ⟨rfl, charValue_mk_iff.2 rfl⟩, ?_⟩
  rintro ⟨c', S⟩ ⟨h₁, h₂⟩
  obtain rfl : c' = c := h₁
  exact Sigma.eq rfl (Subtype.ext (charValue_mk_iff.1 h₂).symm)

/-- A non-trivial component has an edge. -/
theorem exists_adj_of_nontrivial {G : SimpleGraph ι} {c : G.ConnectedComponent} (hc : c.supp.Nontrivial) :
    ∃ i ∈ c.supp, ∃ j ∈ c.supp, G.Adj i j := by
  obtain ⟨i₀, hi₀, i₁, hi₁, hne⟩ := hc
  obtain ⟨p⟩ : G.Reachable i₀ i₁ := SimpleGraph.ConnectedComponent.eq.1 (hi₀.trans (Eq.symm hi₁))
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ j _ hj _ =>
    refine ⟨i₀, hi₀, j, ?_, hj⟩
    have : G.connectedComponentMk i₀ = G.connectedComponentMk j := SimpleGraph.ConnectedComponent.eq.2 hj.reachable
    exact this.symm.trans hi₀

/-- **Line 281** (`g:four_chars`). "For any non-trivial connected component `C`, the submatrix `M(C)` contains at least
four distinct sequences". -/
theorem four_le_card_restrictRows {M : Finset (ι → Bool)} {c : (incompatGraph M).ConnectedComponent}
    (hc : c.supp.Nontrivial) : 4 ≤ (restrictRows c.supp M).card := by
  obtain ⟨i, hi, j, hj, hij⟩ := exists_adj_of_nontrivial hc
  have hij' : ∀ ab : Bool × Bool, ∃ r ∈ M, r i = ab.1 ∧ r j = ab.2 := fun ab => hij ab.1 ab.2
  choose r hr hri hrj using hij'
  have hcard : (Finset.univ : Finset (Bool × Bool)).card ≤ (restrictRows c.supp M).card := by
    refine Finset.card_le_card_of_injOn (fun ab => c.supp.domRestrict (r ab))
      (fun ab _ => mem_restrictRows.2 ⟨r ab, hr ab, rfl⟩) ?_
    intro ab _ ab' _ h
    have h₁ : r ab i = r ab' i := congrFun h ⟨i, hi⟩
    have h₂ : r ab j = r ab' j := congrFun h ⟨j, hj⟩
    rw [hri, hri] at h₁
    rw [hrj, hrj] at h₂
    exact Prod.ext h₁ h₂
  simpa using hcard

/-- **Lemma 3** (`g:lem3`). "No pair of characters of `B` are incompatible" (line 256). -/
theorem lemma3 (M : Finset (ι → Bool)) (p q : SuperChar M) : ¬ Incompatible (matrixB M) p q := by
  intro hinc
  have key : ∀ a b, ∃ r ∈ M, charValue p r = a ∧ charValue q r = b := by
    intro a b
    obtain ⟨r, hr, h₁, h₂⟩ := hinc a b
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hr
    exact ⟨r', hr', h₁, h₂⟩
  obtain ⟨c, S⟩ := p
  obtain ⟨c', S'⟩ := q
  by_cases hcc : c = c'
  · -- `p` and `q` originate from the same connected component.
    subst hcc
    by_cases hS : S = S'
    · subst hS
      obtain ⟨r, -, h₁, h₂⟩ := key true false
      simp [h₁] at h₂
    · obtain ⟨r, -, h₁, h₂⟩ := key true true
      exact hS (Subtype.ext ((charValue_mk_iff.1 h₁).symm.trans (charValue_mk_iff.1 h₂)))
  · -- They originate from two different connected components.
    obtain ⟨d, d', hd⟩ := (theorem2 M hcc).1
    by_cases h₁ : S.1 = d <;> by_cases h₂ : S'.1 = d'
    · -- Both dominant: no `0, 0`.
      obtain ⟨r, hr, ha, hb⟩ := key false false
      rcases corollary1 M hcc hd hr with h | h
      · exact domRestrict_ne_of_charValue_eq_false ha (h.trans h₁.symm)
      · exact domRestrict_ne_of_charValue_eq_false hb (h.trans h₂.symm)
    · -- `p` dominant, `q` not: no `0, 1`.
      obtain ⟨r, hr, ha, hb⟩ := key false true
      rcases corollary1 M hcc hd hr with h | h
      · exact domRestrict_ne_of_charValue_eq_false ha (h.trans h₁.symm)
      · exact h₂ ((charValue_mk_iff.1 hb).symm.trans h)
    · -- The symmetric case: no `1, 0`.
      obtain ⟨r, hr, ha, hb⟩ := key true false
      rcases corollary1 M hcc hd hr with h | h
      · exact h₁ ((charValue_mk_iff.1 ha).symm.trans h)
      · exact domRestrict_ne_of_charValue_eq_false hb (h.trans h₂.symm)
    · -- Both non-dominant: no `1, 1`.
      obtain ⟨r, hr, ha, hb⟩ := key true true
      rcases corollary1 M hcc hd hr with h | h
      · exact h₁ ((charValue_mk_iff.1 ha).symm.trans h)
      · exact h₂ ((charValue_mk_iff.1 hb).symm.trans h)

/-- **Line 264** (`g:tbar`). "Applying the Perfect Phylogeny Theorem, Lemma 3 establishes that there is a perfect phylogeny
`T̄` where each character of `B` labels one edge in `T̄`, and each edge is labeled by one or more characters of `B`". Each
edge here is each internal edge, by the reading of `IsTBar`.

A remark on line 271: "all columns in `B` are distinct" isn't so, since a trivial component gives two columns with one
bipartition, and columns from different components can have one bipartition. What the proof uses is that splits of edges
are distinct, which is a part of `IsTBar`.

The Perfect Phylogeny Theorem gives a tree that can have unlabelled internal edges and nodes of degree two. The paper doesn't
address this; `IsPerfectPhylogeny.exists_normal` contracts the edges that aren't needed. -/
theorem exists_isTBar [Finite ι] (M : Finset (ι → Bool)) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : M → Fin n) (edge : SuperChar M → Sym2 (Fin n)), IsTBar M T φ edge := by
  have : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  have : Finite (incompatGraph M).ConnectedComponent :=
    Finite.of_surjective (incompatGraph M).connectedComponentMk fun c => c.exists_rep
  have hA : ∀ k : SuperChar M, ∃ x y : M, charValue k (x : ι → Bool) ≠ charValue k (y : ι → Bool) := by
    rintro ⟨c, S⟩
    obtain ⟨r, hr, hrS⟩ := mem_restrictRows.1 S.2
    obtain ⟨i, hi⟩ := c.exists_rep
    obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hC i
    have hval : charValue (⟨c, S⟩ : SuperChar M) r = true := charValue_mk_iff.2 hrS
    by_cases h₁ : charValue (⟨c, S⟩ : SuperChar M) r₁ = true
    · refine ⟨⟨r₂, hr₂⟩, ⟨r₁, hr₁⟩, ?_⟩
      rw [h₁]
      intro h₂
      have h₃ : c.supp.domRestrict r₂ = c.supp.domRestrict r₁ :=
        (charValue_mk_iff.1 (h₂ : charValue (⟨c, S⟩ : SuperChar M) r₂ = true)).trans (charValue_mk_iff.1 h₁).symm
      exact hne (congrFun h₃ ⟨i, hi⟩).symm
    · exact ⟨⟨r, hr⟩, ⟨r₁, hr₁⟩, by rw [show charValue (⟨c, S⟩ : SuperChar M) (r : ι → Bool) = true from hval]; exact Ne.symm h₁⟩
  have hinc : ∀ k l : SuperChar M, ∃ a b, ∀ x : M, ¬ (charValue k (x : ι → Bool) = a ∧ charValue l (x : ι → Bool) = b) := by
    intro k l
    have := lemma3 M k l
    unfold Incompatible at this
    push Not at this
    obtain ⟨a, b, h⟩ := this
    refine ⟨a, b, fun x hx => ?_⟩
    exact h _ (Finset.mem_image_of_mem _ x.2) hx.1 hx.2
  obtain ⟨n₀, T₀, φ₀, edge₀, h₀⟩ :=
    (Gusfield1991.exists_isPerfectPhylogeny_iff (fun (r : M) (k : SuperChar M) => charValue k (r : ι → Bool)) hA).2 hinc
  obtain ⟨W, _, T₁, φ₁, edge₁, h₁, h₂, h₃⟩ := h₀.exists_normal
  obtain ⟨n, T, φ, edge, h₄, h₅, h₆⟩ := h₁.exists_fin h₂ h₃
  exact ⟨n, T, φ, edge, { h₄ with internal_labelled := h₅, degree_ne_two := h₆ }⟩

section TBar

variable {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W} {edge : SuperChar M → Sym2 W}

/-- A column of `B` has a side function on `T̄` with value the state of the column at each row: the "1-side" and "0-side" of line
271. -/
theorem IsTBar.exists_side (h : IsTBar M T φ edge) (k : SuperChar M) :
    ∃ σ, IsCut T (edge k) σ ∧ ∀ r : M, σ (φ r) = charValue k (r : ι → Bool) := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  have hφ : ∀ v, (T.neighborSet v).ncard ≤ 1 → v ∈ Set.range φ := fun v => (h.mem_range_iff v).2
  obtain ⟨s, hs⟩ := exists_isCut hT (h.edge_mem k)
  have hmem := h.edge_mem k
  induction he : edge k with
  | h a b =>
    rw [he] at hmem hs
    have hab : T.Adj a b := hmem
    obtain ⟨x₀, hx₀⟩ := exists_row_side hT hφ hab hs
    have hspl : ∀ y : M, charValue k (x₀ : ι → Bool) = charValue k (y : ι → Bool) ↔ s (φ x₀) = s (φ y) := by
      intro y
      rw [← hs.sameSide_iff hconn hab, ← he]
      exact h.split k x₀ y
    refine ⟨fun w => if s w = s (φ x₀) then charValue k (x₀ : ι → Bool) else !charValue k (x₀ : ι → Bool), ?_, fun y => ?_⟩
    · intro u v huv
      rw [← hs huv]
      beta_reduce
      cases s u <;> cases s v <;> cases s (φ x₀) <;> cases charValue k (x₀ : ι → Bool) <;> simp
    · beta_reduce
      by_cases h₁ : s (φ y) = s (φ x₀)
      · simp only [h₁, ↓reduceIte]
        exact (hspl y).2 h₁.symm
      · simp only [h₁, ↓reduceIte]
        have h₂ := mt (hspl y).1 (Ne.symm h₁)
        cases h₃ : charValue k (x₀ : ι → Bool) <;> cases h₄ : charValue k (y : ι → Bool) <;> simp_all

omit [Finite W] in
/-- `T̄` with its rows is an `X`-tree: a node of degree at most two is labelled, since no node has degree two. -/
theorem IsTBar.labelled (h : IsTBar M T φ edge) (v : W) (hv : (T.neighborSet v).ncard ≤ 2) : v ∈ Set.range φ :=
  (h.mem_range_iff v).2 (by
    have := h.degree_ne_two v
    omega)

/-- Distinct edges of `T̄` have distinct splits: line 271's "all the splits defined by the edges in `T̄` are distinct". -/
theorem IsTBar.edge_eq_of_split (h : IsTBar M T φ edge) {e f : Sym2 W} (he : e ∈ T.edgeSet) (hf : f ∈ T.edgeSet) {s t : W → Bool}
    (hs : IsCut T e s) (ht : IsCut T f t) (hsplit : ∀ x y, s (φ x) = s (φ y) ↔ t (φ x) = t (φ y)) : e = f := by
  have hconn := h.isTree.connected.preconnected
  exact edge_eq_of_sameSide_iff h.isTree h.labelled he fun x y => by
    rw [hs.sameSide_iff hconn he, ht.sameSide_iff hconn hf]
    exact hsplit x y

omit [Finite W] in
/-- `T̄` as an `X`-tree in the sense of Semple and Steel. -/
theorem IsTBar.isXTree (h : IsTBar M T φ edge) : SempleSteel2003.IsXTree T φ where
  isTree := h.isTree
  labelled v hv := (h.mem_range_iff v).2 (by
    have := h.degree_ne_two v
    omega)

/-- A row is alone on its side of its pendant edge. -/
theorem IsTBar.pendant_side (h : IsTBar M T φ edge) {x : M} {a : W} (ha : T.Adj (φ x) a) {s : W → Bool}
    (hs : IsCut T s(φ x, a) s) (z : M) : s (φ z) = s (φ x) ↔ z = x := by
  refine ⟨fun hz => ?_, fun hz => by rw [hz]⟩
  have huniq : ∀ c, T.Adj (φ x) c → c = a := fun c hc =>
    (Set.ncard_le_one_iff (Set.toFinite _)).1 ((h.mem_range_iff _).1 ⟨x, rfl⟩) hc ha
  exact h.label_injective (sameSide_pendant huniq (hs.sameSide_of_eq h.isTree.connected.preconnected ha hz.symm))

/-- Each split of `T̄` is a split of any other `T̄` for `M`. -/
theorem IsTBar.splitSides_subset {W' : Type*} [Finite W'] {T' : SimpleGraph W'} {φ' : M → W'} {edge' : SuperChar M → Sym2 W'}
    (h : IsTBar M T φ edge) (h' : IsTBar M T' φ' edge') : SempleSteel2003.splitSides T φ ⊆ SempleSteel2003.splitSides T' φ' := by
  have hconn := h.isTree.connected.preconnected
  have hconn' := h'.isTree.connected.preconnected
  have key : ∀ (r : M) (a : W), T.Adj (φ r) a → ∀ x, SempleSteel2003.edgeSide T φ s(φ r, a) x ∈ SempleSteel2003.splitSides T' φ' := by
    intro r a hra x
    obtain ⟨s, hs⟩ := exists_isCut h.isTree (show s(φ r, a) ∈ T.edgeSet from hra)
    have hs₁ := h.pendant_side hra hs
    obtain ⟨y, hy⟩ := exists_row_side h.isTree (fun v => (h.mem_range_iff v).2) hra.symm (by rwa [Sym2.eq_swap])
    have hyr : r ≠ y := by
      rintro rfl
      exact hs.ne_self hra hy
    have hne' : φ' r ≠ φ' y := fun heq => hyr (h'.label_injective heq)
    obtain ⟨w, hw, -⟩ := exists_adj_separating h'.isTree hne'
    obtain ⟨s', hs'⟩ := exists_isCut h'.isTree (show s(φ' r, w) ∈ T'.edgeSet from hw)
    have hs₁' := h'.pendant_side hw hs'
    refine ⟨s(φ' r, w), hw, x, ?_⟩
    ext z
    change SameSide T _ (φ x) (φ z) ↔ SameSide T' _ (φ' x) (φ' z)
    rw [hs.sameSide_iff hconn hra, hs'.sameSide_iff hconn' hw]
    exact split_eq_of_single (f := s ∘ φ) (g := s' ∘ φ') hs₁ hs₁' x z
  rintro A ⟨e, he, x, rfl⟩
  induction e with
  | h a b =>
    have hab : T.Adj a b := he
    by_cases ha : a ∈ Set.range φ
    · obtain ⟨r, rfl⟩ := ha
      exact key r b hab x
    by_cases hb : b ∈ Set.range φ
    · obtain ⟨r, rfl⟩ := hb
      rw [Sym2.eq_swap]
      exact key r a hab.symm x
    obtain ⟨k, hk⟩ := h.internal_labelled a b hab ha hb
    refine ⟨edge' k, h'.edge_mem k, x, ?_⟩
    ext z
    change SameSide T _ (φ x) (φ z) ↔ SameSide T' _ (φ' x) (φ' z)
    rw [← hk]
    exact (h.split k x z).symm.trans (h'.split k x z)

/-- **Lines 156, 344** (`g:tbar_unique`). `T̄` is unique: "the splits of an undirected tree uniquely define the tree". -/
theorem isTBar_unique {M : Finset (ι → Bool)} {W W' : Type*} [Finite ι] [Finite W] [Finite W'] (hM : M.Nonempty)
    {T : SimpleGraph W} {T' : SimpleGraph W'} {φ : M → W} {φ' : M → W'} {edge : SuperChar M → Sym2 W}
    {edge' : SuperChar M → Sym2 W'} (h : IsTBar M T φ edge) (h' : IsTBar M T' φ' edge') :
    ∃ f : T ≃g T', ∀ r, f (φ r) = φ' r := by
  have : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  exact SempleSteel2003.xTree_unique h.isXTree h'.isXTree
    (subset_antisymm (h.splitSides_subset h') (h'.splitSides_subset h))

theorem exists_charValue_eq_true (k : SuperChar M) : ∃ r : M, charValue k (r : ι → Bool) = true := by
  obtain ⟨c, S⟩ := k
  obtain ⟨r, hr, hrS⟩ := mem_restrictRows.1 S.2
  exact ⟨⟨r, hr⟩, charValue_mk_iff.2 hrS⟩

/-- "No leaf in `T̄` can be on the 1-side of two of the edges", line 283. -/
theorem charValue_disjoint {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1) {r : ι → Bool}
    (h₁ : charValue k r = true) (h₂ : charValue k' r = true) : False := by
  obtain ⟨c, S⟩ := k
  obtain ⟨c', S'⟩ := k'
  obtain rfl : c = c' := hc
  exact hne (Sigma.eq rfl (Subtype.ext ((charValue_mk_iff.1 h₁).symm.trans (charValue_mk_iff.1 h₂))))

/-- The 1-sides of two characters from one component are disjoint: "the 1-sides of both `e₁` and `e₂` point 'away' from each
other" (line 287). -/
theorem IsTBar.not_both_one (h : IsTBar M T φ edge) {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1) {σ σ' : W → Bool}
    (hσ : IsCut T (edge k) σ) (hσ' : IsCut T (edge k') σ') (hr : ∀ r : M, σ (φ r) = charValue k (r : ι → Bool))
    (hr' : ∀ r : M, σ' (φ r) = charValue k' (r : ι → Bool)) (w : W) : ¬ (σ w = true ∧ σ' w = true) := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  have hdis : ∀ r : M, ¬ (σ (φ r) = true ∧ σ' (φ r) = true) := fun r hb =>
    charValue_disjoint hne hc (by rw [← hr]; exact hb.1) (by rw [← hr']; exact hb.2)
  obtain ⟨r₁, hr₁⟩ := exists_charValue_eq_true k
  obtain ⟨r₂, hr₂⟩ := exists_charValue_eq_true k'
  rw [← hr] at hr₁
  rw [← hr'] at hr₂
  have hr₁' : σ' (φ r₁) = false := by
    cases h₁ : σ' (φ r₁)
    · rfl
    · exact absurd ⟨hr₁, h₁⟩ (hdis r₁)
  have hr₂' : σ (φ r₂) = false := by
    cases h₁ : σ (φ r₂)
    · rfl
    · exact absurd ⟨h₁, hr₂⟩ (hdis r₂)
  by_cases hee : edge k = edge k'
  · -- One edge: the two functions are cuts of one edge, and they differ at `r₁`.
    have hmem := h.edge_mem k
    rintro ⟨h₁, h₂⟩
    rw [← hee] at hσ'
    induction he : edge k with
    | h a b =>
      rw [he] at hmem hσ hσ'
      rcases IsCut.eq_or_eq_not hT hmem hσ hσ' with hall | hall
      · rw [hall, hr₁'] at hr₁
        exact absurd hr₁ (by simp)
      · rw [hall, h₂] at h₁
        exact absurd h₁ (by simp)
  · -- Two edges: a leaf is on the 0-side of both, or they'd have one split.
    have hl : ∃ l : M, σ (φ l) = false ∧ σ' (φ l) = false := by
      by_contra hcon
      push Not at hcon
      exact hee (h.edge_eq_of_split (h.edge_mem k) (h.edge_mem k') hσ hσ'
        (split_iff_of_iff (f := σ ∘ φ) (g := σ' ∘ φ) (c := true) (d := false)
          fun x => bool_iff_of_not_both (hdis x) (hcon x)))
    obtain ⟨l, hl₁, hl₂⟩ := hl
    exact IsCut.not_fourth hconn hσ hσ' (h.edge_mem k) (h.edge_mem k') hee (a := false) (b := false)
      (x := φ l) (y := φ r₂) (z := φ r₁) ⟨hl₁, hl₂⟩ ⟨hr₂', hr₂⟩ ⟨hr₁, hr₁'⟩

/-- Two characters from a non-trivial component label distinct edges (the paper's `e₁`, `e₂`, line 285): if not, each row
would have one of two super-characters, and `M(C)` has at least four. -/
theorem IsTBar.edge_ne (h : IsTBar M T φ edge) {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1)
    (hnt : k.1.supp.Nontrivial) : edge k ≠ edge k' := by
  intro hee
  have hT := h.isTree
  obtain ⟨σ, hσ, hr⟩ := h.exists_side k
  obtain ⟨σ', hσ', hr'⟩ := h.exists_side k'
  obtain ⟨r₁, hr₁⟩ := exists_charValue_eq_true k
  have hmem := h.edge_mem k
  rw [← hee] at hσ'
  have hall : ∀ x, σ x = !σ' x := by
    induction he : edge k with
    | h a b =>
      rw [he] at hmem hσ hσ'
      rcases IsCut.eq_or_eq_not hT hmem hσ hσ' with hall | hall
      · exfalso
        have h₁ : σ' (φ r₁) = true := by rw [← hall, hr, hr₁]
        exact charValue_disjoint hne hc hr₁ (by rw [← hr']; exact h₁)
      · exact hall
  -- So each row contains one of the two super-characters.
  obtain ⟨c, S⟩ := k
  obtain ⟨c', S'⟩ := k'
  obtain rfl : c = c' := hc
  have hsub : restrictRows c.supp M ⊆ {S.1, S'.1} := by
    intro t ht
    obtain ⟨r, hr₀, rfl⟩ := mem_restrictRows.1 ht
    have h₁ := hall (φ ⟨r, hr₀⟩)
    rw [hr, hr'] at h₁
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h₂ : charValue (⟨c, S⟩ : SuperChar M) r = true
    · exact Or.inl (charValue_mk_iff.1 h₂)
    · right
      have h₃ : charValue (⟨c, S'⟩ : SuperChar M) r = true := by
        cases h₄ : charValue (⟨c, S'⟩ : SuperChar M) r
        · simp_all
        · rfl
      exact charValue_mk_iff.1 h₃
  have h₁ := Finset.card_le_card hsub
  have h₂ : 4 ≤ (restrictRows c.supp M).card := four_le_card_restrictRows hnt
  have h₃ : ({S.1, S'.1} : Finset _).card ≤ 2 := Finset.card_le_two
  omega

omit [Finite W] in
/-- The ends of the edge of a character: the end on the 0-side, and the end on the 1-side. -/
theorem IsTBar.exists_ends (h : IsTBar M T φ edge) (k : SuperChar M) {σ : W → Bool} (hσ : IsCut T (edge k) σ) :
    ∃ a b, edge k = s(a, b) ∧ T.Adj a b ∧ σ a = false ∧ σ b = true := by
  have hmem := h.edge_mem k
  induction he : edge k with
  | h a b =>
    rw [he] at hmem hσ
    have hab : T.Adj a b := hmem
    have hne := hσ.ne_self hab
    cases h₁ : σ a
    · exact ⟨a, b, rfl, hab, h₁, by cases h₂ : σ b <;> simp_all⟩
    · exact ⟨b, a, Sym2.eq_swap, hab.symm, by cases h₂ : σ b <;> simp_all, h₁⟩

/-- The heart of Lemma 4 (line 285 to line 295): two edges labelled by characters from a non-trivial component are incident with each other. If not, the paper takes the path `P` between them; their 1-sides
point away from each other, so `P` joins the ends `a₁`, `a₂` on the 0-sides. The paper's `e₁`, `e₂` are the edges of `k₁`, `k₂`, and `e` is the edge of `P` at `a₁`.

Departure from the paper: the paper gives Case 1 and says that "the three other cases are similar". The two where `e₁` has a non-dominant super-character take another argument: all the rows beyond `e` have
the dominant super-character, which must be that of `e₂`, and so `e` and `e₂` would have one split. It's needed since the argument of Case 1 gives no contradiction in those two cases. -/
theorem IsTBar.edges_incident (h : IsTBar M T φ edge) {k₁ k₂ : SuperChar M} (hne : k₁ ≠ k₂) (hc : k₁.1 = k₂.1)
    (hnt : k₁.1.supp.Nontrivial) : ∃ v, v ∈ edge k₁ ∧ v ∈ edge k₂ := by
  obtain ⟨σ₁, hσ₁, hr₁⟩ := h.exists_side k₁
  obtain ⟨σ₂, hσ₂, hr₂⟩ := h.exists_side k₂
  obtain ⟨a₁, b₁, h₁, hab₁, hs₁a, hs₁b⟩ := h.exists_ends k₁ hσ₁
  obtain ⟨a₂, b₂, h₂, hab₂, hs₂a, hs₂b⟩ := h.exists_ends k₂ hσ₂
  by_contra hno
  have hneq : a₁ ≠ a₂ := by
    rintro rfl
    exact hno ⟨a₁, by rw [h₁]; simp, by rw [h₂]; simp⟩
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  have hee : edge k₁ ≠ edge k₂ := h.edge_ne hne hc hnt
  have hboth := h.not_both_one hne hc hσ₁ hσ₂ hr₁ hr₂
  -- `a₁`, `a₂` are on the 0-side of both edges.
  have h₂b₁ : σ₂ b₁ = false := by
    cases h' : σ₂ b₁
    · rfl
    · exact absurd ⟨hs₁b, h'⟩ (hboth b₁)
  have h₁b₂ : σ₁ b₂ = false := by
    cases h' : σ₁ b₂
    · rfl
    · exact absurd ⟨h', hs₂b⟩ (hboth b₂)
  have h₂a₁ : σ₂ a₁ = false := by
    rw [← h₂b₁]
    exact hσ₂.eq_of_ne hab₁ (h₁ ▸ hee)
  have h₁a₂ : σ₁ a₂ = false := by
    rw [← h₁b₂]
    exact hσ₁.eq_of_ne hab₂ (h₂ ▸ Ne.symm hee)
  -- The edge `e` at `a₁` towards `a₂`.
  obtain ⟨w, hw, hsep, hsame, -⟩ := exists_adj_separating hT hneq
  have he₁ : s(a₁, w) ≠ edge k₁ := by
    intro heq
    apply hsep
    rw [heq]
    rw [← heq] at hσ₁
    rw [← heq]
    exact hσ₁.sameSide_of_eq hconn hw (hs₁a.trans h₁a₂.symm)
  have he₂ : s(a₁, w) ≠ edge k₂ := by
    intro heq
    apply hsep
    rw [← heq] at hσ₂
    exact hσ₂.sameSide_of_eq hconn hw (h₂a₁.trans hs₂a.symm)
  have hwb₁ : w ≠ b₁ := by
    rintro rfl
    exact he₁ h₁.symm
  -- `e` is an internal edge, so it's labelled.
  have ha₁ : a₁ ∉ Set.range φ := by
    intro hmem
    have hd := (h.mem_range_iff a₁).1 hmem
    exact hwb₁ ((Set.ncard_le_one_iff (Set.toFinite _)).1 hd hw hab₁)
  have hw' : w ∉ Set.range φ := by
    intro hmem
    have hd := (h.mem_range_iff w).1 hmem
    have huniq : ∀ {u}, T.Adj w u → u = a₁ := fun {u} hu =>
      (Set.ncard_le_one_iff (Set.toFinite _)).1 hd hu hw.symm
    by_cases hwa : w = a₂
    · subst hwa
      have := huniq hab₂
      subst this
      rw [hs₂b] at h₂a₁
      exact absurd h₂a₁ (by simp)
    · obtain ⟨w', hw', hsep', -⟩ := exists_adj_separating hT hwa
      have := huniq hw'
      subst this
      rw [Sym2.eq_swap] at hsep'
      exact hsep' hsame
  obtain ⟨k', hk'⟩ := h.internal_labelled _ _ hw ha₁ hw'
  obtain ⟨σ', hσ', hr'⟩ := h.exists_side k'
  have hσ'' : IsCut T s(a₁, w) σ' := hk' ▸ hσ'
  have hsepa : σ' a₁ ≠ σ' a₂ := fun heq => hsep (hσ''.sameSide_of_eq hconn hw heq)
  have hwa₂ : σ' w = σ' a₂ := hσ''.eq_of_sameSide hsame
  have hee₁ : edge k' ≠ edge k₁ := hk' ▸ he₁
  have hee₂ : edge k' ≠ edge k₂ := hk' ▸ he₂
  have hb₁a : σ' a₁ = σ' b₁ := hσ'.eq_of_ne hab₁ (h₁ ▸ Ne.symm hee₁)
  have hb₂a : σ' a₂ = σ' b₂ := hσ'.eq_of_ne hab₂ (h₂ ▸ Ne.symm hee₂)
  by_cases hk'c : k'.1 = k₁.1
  · -- `P` can't go through the edge of a third character from `C`.
    have hk₁' : k' ≠ k₁ := fun heq => hee₁ (by rw [heq])
    have hk₂' : k' ≠ k₂ := fun heq => hee₂ (by rw [heq])
    have h₃ := h.not_both_one hk₁' hk'c hσ' hσ₁ hr' hr₁ b₁
    have h₄ := h.not_both_one hk₂' (hk'c.trans hc) hσ' hσ₂ hr' hr₂ b₂
    have h₅ : σ' a₁ = false := by
      cases h₆ : σ' a₁
      · rfl
      · exact absurd ⟨hb₁a ▸ h₆, hs₁b⟩ h₃
    have h₆ : σ' a₂ = false := by
      cases h₇ : σ' a₂
      · rfl
      · exact absurd ⟨hb₂a ▸ h₇, hs₂b⟩ h₄
    exact hsepa (h₅.trans h₆.symm)
  · -- The edge `e` is labelled by a character from another component `C'`.
    set A := σ' a₁ with hA
    have hwA : σ' w = !A := by rw [hwa₂]; exact nb hsepa
    have hconn₁ : ∀ x, ¬ (σ₁ x = true ∧ σ' x = !A) := fun x =>
      IsCut.not_fourth hconn hσ₁ hσ' (h.edge_mem k₁) (h.edge_mem k') (Ne.symm hee₁) (a := false) (b := A)
        (x := a₁) (y := w) (z := b₁) ⟨hs₁a, rfl⟩
        ⟨(hσ₁.eq_of_ne hw he₁).symm.trans hs₁a, hwA⟩ ⟨hs₁b, hb₁a.symm⟩
    have hconn₂ : ∀ x, ¬ (σ₂ x = true ∧ σ' x = A) := fun x => by
      have hb₂A : σ' b₂ = !A := by rw [← hb₂a]; exact nb hsepa
      have ha₂A : σ' a₂ = !A := nb hsepa
      have := IsCut.not_fourth hconn hσ₂ hσ' (h.edge_mem k₂) (h.edge_mem k') (Ne.symm hee₂) (a := false) (b := !A)
        (x := a₂) (y := a₁) (z := b₂) (w := x) ⟨hs₂a, ha₂A⟩ ⟨h₂a₁, by simp [hA]⟩ ⟨hs₂b, hb₂A⟩
      simpa using this
    -- A leaf on the near side of both `e` and `e₁`, or they'd have one split.
    obtain ⟨l, hl₁, hl₂⟩ : ∃ l : M, σ₁ (φ l) = false ∧ σ' (φ l) = A := by
      by_contra hcon
      push Not at hcon
      have hiff : ∀ x : M, σ₁ (φ x) = true ↔ σ' (φ x) = A := fun x => by
        have hx := hcon x
        have hx' := hconn₁ (φ x)
        revert hx hx'
        cases σ₁ (φ x) <;> cases σ' (φ x) <;> cases A <;> simp
      exact hee₁ (h.edge_eq_of_split (h.edge_mem k₁) (h.edge_mem k') hσ₁ hσ'
        (split_iff_of_iff (f := σ₁ ∘ φ) (g := σ' ∘ φ) hiff)).symm
    -- A leaf beyond `e`.
    obtain ⟨z, hz⟩ := exists_row_side hT (fun v => (h.mem_range_iff v).2) hw.symm (by rwa [Sym2.eq_swap] : IsCut T s(w, a₁) σ')
    rw [hwA] at hz
    have hz₁ : σ₁ (φ z) = false := by
      cases h' : σ₁ (φ z)
      · rfl
      · exact absurd ⟨h', hz⟩ (hconn₁ _)
    -- The dominant sequences of `C`, `C'`.
    obtain ⟨c, S₁⟩ := k₁
    obtain ⟨c₂, S₂⟩ := k₂
    obtain ⟨c', S'⟩ := k'
    obtain rfl : c = c₂ := hc
    have hcc : c ≠ c' := fun heq => hk'c heq.symm
    obtain ⟨d, d', hd⟩ := (theorem2 M hcc).1
    have hcor : ∀ r : M, c.supp.domRestrict (r : ι → Bool) = d ∨ c'.supp.domRestrict (r : ι → Bool) = d' :=
      fun r => corollary1 M hcc hd r.2
    obtain ⟨r₁, hrow₁⟩ := exists_charValue_eq_true (⟨c, S₁⟩ : SuperChar M)
    obtain ⟨r₂, hrow₂⟩ := exists_charValue_eq_true (⟨c, S₂⟩ : SuperChar M)
    by_cases hS₁ : S₁.1 = d
    · -- `e₁` is `e(S)`: the cases 1 and 2 of the paper.
      have hl₃ : c.supp.domRestrict (l : ι → Bool) ≠ d := by
        have := domRestrict_ne_of_charValue_eq_false (r := (l : ι → Bool)) (by rw [← hr₁]; exact hl₁)
        rwa [hS₁] at this
      have hl₄ := (hcor l).resolve_left hl₃
      have hz₃ : c.supp.domRestrict (z : ι → Bool) ≠ d := by
        have := domRestrict_ne_of_charValue_eq_false (r := (z : ι → Bool)) (by rw [← hr₁]; exact hz₁)
        rwa [hS₁] at this
      have hz₄ := (hcor z).resolve_left hz₃
      by_cases hS' : S'.1 = d'
      · -- Case 1. The leaf `l_v` is on the 1-side of `e`, so `z` is on the 0-side of both.
        have h₃ : σ' (φ l) = true := by
          rw [hr']
          exact charValue_mk_iff.2 (hl₄.trans hS'.symm)
        have h₄ : σ' (φ z) = true := by
          rw [hr']
          exact charValue_mk_iff.2 (hz₄.trans hS'.symm)
        rw [hl₂] at h₃
        rw [hz, h₃] at h₄
        exact absurd h₄ (by simp)
      · -- Case 2. The leaf `l_v` is on the 0-side of `e`, so `z` is on the 1-side of `e`.
        have h₃ : σ' (φ l) = false := by
          rw [hr']
          cases h₄ : charValue (⟨c', S'⟩ : SuperChar M) (l : ι → Bool)
          · rfl
          · exact absurd ((charValue_mk_iff.1 h₄).symm.trans hl₄) hS'
        have h₄ : σ' (φ z) = false := by
          rw [hr']
          cases h₅ : charValue (⟨c', S'⟩ : SuperChar M) (z : ι → Bool)
          · rfl
          · exact absurd ((charValue_mk_iff.1 h₅).symm.trans hz₄) hS'
        rw [hl₂] at h₃
        rw [hz, h₃] at h₄
        exact absurd h₄ (by simp)
    · -- `e₁` isn't `e(S)`: the cases 3 and 4. Every row beyond `e` has the dominant sequence of `C`.
      have hrow₃ : c.supp.domRestrict (r₁ : ι → Bool) = S₁.1 := charValue_mk_iff.1 hrow₁
      have hrow₄ : c'.supp.domRestrict (r₁ : ι → Bool) = d' :=
        (hcor r₁).resolve_left fun h₅ => hS₁ (hrow₃.symm.trans h₅)
      have hrA : σ' (φ r₁) = A := by
        have h₅ := hconn₁ (φ r₁)
        have h₆ : σ₁ (φ r₁) = true := by rw [hr₁]; exact hrow₁
        rw [h₆] at h₅
        revert h₅
        cases σ' (φ r₁) <;> cases A <;> simp
      have hbeyond : ∀ y : M, σ' (φ y) = !A → c.supp.domRestrict (y : ι → Bool) = d := by
        intro y hy
        by_contra hcon
        have hy₁ := (hcor y).resolve_left hcon
        rw [hr'] at hy hrA
        have hsame' : charValue (⟨c', S'⟩ : SuperChar M) (y : ι → Bool) =
            charValue (⟨c', S'⟩ : SuperChar M) (r₁ : ι → Bool) := by
          simp only [charValue, hy₁, hrow₄]
        rw [hsame', hrA] at hy
        cases h₅ : A <;> simp [h₅] at hy
      -- The row of `e₂` is beyond `e`, so `S₂` is dominant, and `e`, `e₂` have one split.
      have hr₂A : σ' (φ r₂) = !A := by
        have h₅ := hconn₂ (φ r₂)
        have h₆ : σ₂ (φ r₂) = true := by rw [hr₂]; exact hrow₂
        rw [h₆] at h₅
        revert h₅
        cases σ' (φ r₂) <;> cases A <;> simp
      have hS₂ : S₂.1 = d := (charValue_mk_iff.1 hrow₂).symm.trans (hbeyond r₂ hr₂A)
      have hiff : ∀ y : M, σ₂ (φ y) = true ↔ σ' (φ y) = !A := by
        intro y
        constructor
        · intro h₅
          have h₆ := hconn₂ (φ y)
          rw [h₅] at h₆
          revert h₆
          cases σ' (φ y) <;> cases A <;> simp
        · intro h₅
          rw [hr₂]
          exact charValue_mk_iff.2 ((hbeyond y h₅).trans hS₂.symm)
      exact hee₂ (h.edge_eq_of_split (h.edge_mem _) (h.edge_mem _) hσ₂ hσ'
        (split_iff_of_iff (f := σ₂ ∘ φ) (g := σ' ∘ φ) hiff)).symm

/-- Line 295: "if there are two distinct edges labeled with characters that originate from `C`, then the 1-sides of these edges point away from each other", and so a node on both
edges is on the 0-side of each. -/
theorem IsTBar.side_eq_false_of_incident (h : IsTBar M T φ edge) {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1)
    (hnt : k.1.supp.Nontrivial) {σ : W → Bool} (hσ : IsCut T (edge k) σ) (hr : ∀ r : M, σ (φ r) = charValue k (r : ι → Bool))
    {v : W} (hv' : v ∈ edge k') : σ v = false := by
  obtain ⟨σ', hσ', hr'⟩ := h.exists_side k'
  have hboth := h.not_both_one hne hc hσ hσ' hr hr'
  obtain ⟨y, hy⟩ := hv'
  have hadj : T.Adj v y := by
    have := h.edge_mem k'
    rwa [hy] at this
  have hcut : IsCut T s(v, y) σ' := hy ▸ hσ'
  have hee : s(v, y) ≠ edge k := by
    rw [← hy]
    exact Ne.symm (h.edge_ne hne hc hnt)
  have hsy : σ v = σ y := hσ.eq_of_ne hadj hee
  have hne' := hcut.ne_self hadj
  cases h₁ : σ v
  · rfl
  · exfalso
    have h₂ : σ' v = false := by
      cases h₃ : σ' v
      · rfl
      · exact absurd ⟨h₁, h₃⟩ (hboth v)
    have h₃ : σ' y = true := by
      rw [h₂] at hne'
      cases h₄ : σ' y
      · simp [h₄] at hne'
      · rfl
    exact hboth y ⟨hsy ▸ h₁, h₃⟩

/-- Two columns from a trivial component have opposite values, and one bipartition (line 245). -/
theorem charValue_ne_of_trivial {k k' : SuperChar M} (hne : k ≠ k') (hc : k.1 = k'.1) (ht : ¬ k.1.supp.Nontrivial)
    (r : ι → Bool) : charValue k r ≠ charValue k' r := by
  obtain ⟨c, S⟩ := k
  obtain ⟨c', S'⟩ := k'
  obtain rfl : c = c' := hc
  have hSS : S.1 ≠ S'.1 := fun heq => hne (Sigma.eq rfl (Subtype.ext heq))
  have hsub : c.supp.Subsingleton := Set.not_nontrivial_iff.1 ht
  have : Subsingleton c.supp := hsub.coe_sort
  obtain ⟨i, hi⟩ : ∃ i, S.1 i ≠ S'.1 i := by
    by_contra hcon
    push Not at hcon
    exact hSS (funext hcon)
  have hval : ∀ f g : c.supp → Bool, f i = g i → f = g := fun f g h =>
    funext fun j => by rwa [Subsingleton.elim j i]
  intro heq
  by_cases h₁ : c.supp.domRestrict r i = S.1 i
  · have h₂ := charValue_mk_iff.2 (hval _ _ h₁)
    rw [heq] at h₂
    have h₃ := charValue_mk_iff.1 h₂
    rw [← h₃] at hSS
    exact hi (h₁.symm.trans (congrFun h₃ i))
  · have h₂ : c.supp.domRestrict r i = S'.1 i := by
      cases h₃ : c.supp.domRestrict r i <;> cases h₄ : S.1 i <;> cases h₅ : S'.1 i <;> simp_all
    have h₃ := charValue_mk_iff.2 (hval _ _ h₂)
    rw [← heq] at h₃
    exact h₁ (congrFun (charValue_mk_iff.1 h₃) i)

/-- **Lemma 4** (`g:lem4`). "Let `C` be an arbitrary component of `G(M)`. In `T̄`, there is a node `v_C` such that all the
edges labeled by characters of `B` that originate from connected component `C`, are incident with `v_C`. [...] Further, `v_C`
is on the 0-side of each split defined by an edge labeled by a character of `B` that originates from `C`" (line 275).

For a trivial component, the paper keeps one of its two columns ("one column can be removed", line 245; "only one
character originates from `C`", line 281). Here both are kept, and they label one edge whose 0-sides are opposite, so the second
clause is for a non-trivial `C`. A trivial `C` has it for each of the columns, at one of the ends of the edge, which is the third
clause.

The proof follows the paper's: pairwise incidence is `IsTBar.edges_incident`, the star is `exists_common_of_pairwise_incident`, and the 0-sides are `IsTBar.side_eq_false_of_incident`. -/
theorem lemma4 {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) (c : (incompatGraph M).ConnectedComponent) :
    ∃ v, (∀ k : SuperChar M, k.1 = c → v ∈ edge k) ∧
      (c.supp.Nontrivial → ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true →
        ¬ SameSide T (edge k) (φ r) v) ∧
      ∀ k : SuperChar M, k.1 = c → ∃ v ∈ edge k, ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v := by
  have hthird : ∀ k : SuperChar M, k.1 = c → ∃ v ∈ edge k, ∀ r : M, charValue k r = true →
      ¬ SameSide T (edge k) (φ r) v := by
    intro k _
    obtain ⟨σ, hσ, hr⟩ := h.exists_side k
    obtain ⟨a, b, he, -, ha, -⟩ := h.exists_ends k hσ
    refine ⟨a, by rw [he]; simp, fun r hk hsame => ?_⟩
    have := hσ.eq_of_sameSide hsame
    rw [hr, hk, ha] at this
    exact absurd this (by simp)
  by_cases hk : ∃ k : SuperChar M, k.1 = c
  · obtain ⟨k₀, hk₀⟩ := hk
    obtain ⟨σ₀, hσ₀, hr₀⟩ := h.exists_side k₀
    obtain ⟨a₀, b₀, he₀, hab₀, ha₀, hb₀⟩ := h.exists_ends k₀ hσ₀
    by_cases hnt : c.supp.Nontrivial
    · -- Every pair of edges labelled by characters from `C` is incident, so they form a star.
      have hincident : ∀ k k' : SuperChar M, k.1 = c → k'.1 = c → ∃ v, v ∈ edge k ∧ v ∈ edge k' := by
        intro k k' hk hk'
        by_cases hkk : k = k'
        · subst hkk
          obtain ⟨σ, hσ, -⟩ := h.exists_side k
          obtain ⟨a, b, he, -⟩ := h.exists_ends k hσ
          exact ⟨a, by rw [he]; simp, by rw [he]; simp⟩
        · exact h.edges_incident hkk (hk.trans hk'.symm) (hk ▸ hnt)
      obtain ⟨v, hv⟩ := exists_common_of_pairwise_incident h.isTree (F := {e | ∃ k : SuperChar M, k.1 = c ∧ e = edge k})
        (by
          rintro e ⟨k, -, rfl⟩
          exact h.edge_mem k)
        ⟨_, k₀, hk₀, rfl⟩
        (by
          rintro e ⟨k, hk, rfl⟩ f ⟨k', hk', rfl⟩
          exact hincident k k' hk hk')
      have hstar : ∀ k : SuperChar M, k.1 = c → v ∈ edge k := fun k hk => hv _ ⟨k, hk, rfl⟩
      refine ⟨v, hstar, fun _ k hkc r hrk hsame => ?_, hthird⟩
      -- There's another character from `C`, as `M(C)` has at least four sequences.
      obtain ⟨c', S⟩ := k
      obtain rfl : c' = c := hkc
      have hcard : 1 < (restrictRows c'.supp M).card := by
        have := four_le_card_restrictRows hnt
        omega
      obtain ⟨S', hS', hne⟩ := Finset.exists_mem_ne hcard S.1
      have hkk : (⟨c', S⟩ : SuperChar M) ≠ ⟨c', ⟨S', hS'⟩⟩ := fun heq =>
        hne (congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.1 heq).2)).symm
      obtain ⟨σ, hσ, hr⟩ := h.exists_side (⟨c', S⟩ : SuperChar M)
      have hzero := h.side_eq_false_of_incident hkk rfl hnt hσ hr (hstar _ rfl)
      have heq := hσ.eq_of_sameSide hsame
      rw [hr, hrk, hzero] at heq
      exact absurd heq (by simp)
    · -- A trivial component: one edge.
      refine ⟨a₀, fun k hkc => ?_, fun hnt' => absurd hnt' hnt, hthird⟩
      by_cases hne : k₀ = k
      · rw [← hne, he₀]; simp
      · obtain ⟨σ, hσ, hr⟩ := h.exists_side k
        have heq : edge k₀ = edge k := by
          refine h.edge_eq_of_split (h.edge_mem _) (h.edge_mem _) hσ₀ hσ fun x y => ?_
          rw [hr₀, hr₀, hr, hr]
          have hc : k₀.1 = k.1 := hk₀.trans hkc.symm
          have ht : ¬ k₀.1.supp.Nontrivial := hk₀ ▸ hnt
          have hx := charValue_ne_of_trivial hne hc ht (x : ι → Bool)
          have hy := charValue_ne_of_trivial hne hc ht (y : ι → Bool)
          revert hx hy
          cases charValue k₀ (x : ι → Bool) <;> cases charValue k (x : ι → Bool) <;>
            cases charValue k₀ (y : ι → Bool) <;> cases charValue k (y : ι → Bool) <;> simp
        rw [← heq, he₀]; simp
  · obtain ⟨v⟩ := h.isTree.connected.nonempty
    refine ⟨v, fun k hkc => absurd ⟨k, hkc⟩ hk, fun _ k hkc => absurd ⟨k, hkc⟩ hk, hthird⟩

/-- **Line 277** (`g:vC_only`). The paper notes that "Lemma 4 does not assert that `v_C` is only incident with edges labeled by
characters that originate from `C`". It is so, for a non-trivial `C`: each other branch at `v_C` would have a leaf, which is on
the 1-side of an edge of the star by line 283, but on its 0-side since it's reached without crossing that edge. Line 299 uses this
fact without stating it ("the edge incident with `v_C` that is labeled by character `c`"), and so the note isn't an error, only a caution.

The proof doesn't use that `C` is non-trivial: `hv'` can only hold then, since the two columns of a trivial component have opposite 0-sides. -/
theorem adj_center_labelled {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) {c : (incompatGraph M).ConnectedComponent}
    (_hc : c.supp.Nontrivial) {v : W} (hv : ∀ k : SuperChar M, k.1 = c → v ∈ edge k)
    (hv' : ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) {u : W}
    (hu : T.Adj v u) : ∃ k : SuperChar M, k.1 = c ∧ edge k = s(v, u) := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  obtain ⟨τ, hτ⟩ := exists_isCut hT (show s(v, u) ∈ T.edgeSet from hu)
  obtain ⟨r, hr⟩ := exists_row_side hT (fun v => (h.mem_range_iff v).2) hu.symm (by rwa [Sym2.eq_swap] : IsCut T s(u, v) τ)
  obtain ⟨k, ⟨hk₁, hk₂⟩, -⟩ := existsUnique_charValue_eq_true c r.2
  refine ⟨k, hk₁, ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ := hv k hk₁
  have hadj : T.Adj v x := by
    have := h.edge_mem k
    rwa [hx] at this
  obtain ⟨σ, hσ⟩ := exists_isCut hT (h.edge_mem k)
  have hσ' : IsCut T s(v, x) σ := hx ▸ hσ
  have hrσ : σ (φ r) ≠ σ v := fun heq =>
    hv' k hk₁ r hk₂ (by rw [hx]; exact hσ'.sameSide_of_eq hconn hadj heq)
  have h₁ : σ v ≠ σ x := hσ'.ne_self hadj
  have h₂ : τ v ≠ τ u := hτ.ne_self hu
  have h₃ : σ v = σ u := hσ.eq_of_ne hu (fun heq => hne heq.symm)
  have h₄ : τ v = τ x := hτ.eq_of_ne hadj (fun heq => hne (hx.trans heq))
  exact IsCut.not_fourth hconn hσ hτ (h.edge_mem k) hu hne (a := σ v) (b := τ v) (x := v) (y := u) (z := x) (w := φ r)
    ⟨rfl, rfl⟩ ⟨h₃.symm, nb h₂⟩ ⟨nb h₁, h₄.symm⟩ ⟨nb (Ne.symm hrσ), by rw [hr, nb h₂]⟩

/-- Distinct non-trivial components have distinct centres: the fact behind "each central-star node" of line 299, where a node
is inflated for one component. The paper doesn't state it. -/
theorem IsTBar.center_ne {M : Finset (ι → Bool)} {W : Type*} [Finite W] {T : SimpleGraph W} {φ : M → W}
    {edge : SuperChar M → Sym2 W} (h : IsTBar M T φ edge) {c c' : (incompatGraph M).ConnectedComponent} (hcc : c ≠ c')
    (hc : c.supp.Nontrivial) {v : W} (hv : ∀ k : SuperChar M, k.1 = c → v ∈ edge k)
    (hv₀ : ∀ k : SuperChar M, k.1 = c → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v)
    (hv' : ∀ k : SuperChar M, k.1 = c' → v ∈ edge k)
    (hv₀' : ∀ k : SuperChar M, k.1 = c' → ∀ r : M, charValue k r = true → ¬ SameSide T (edge k) (φ r) v) : False := by
  have hT := h.isTree
  have hconn := hT.connected.preconnected
  have nb : ∀ {α β : Bool}, α ≠ β → β = !α := by decide
  obtain ⟨d, d', hd⟩ := (theorem2 M hcc).1
  -- Two non-dominant super-characters of `C`.
  have hcard : 1 < ((restrictRows c.supp M).erase d).card := by
    have h₁ := four_le_card_restrictRows hc
    have h₂ := Finset.pred_card_le_card_erase (s := restrictRows c.supp M) (a := d)
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := Finset.one_lt_card.1 hcard
  obtain ⟨ht₁d, ht₁M⟩ := Finset.mem_erase.1 ht₁
  obtain ⟨ht₂d, ht₂M⟩ := Finset.mem_erase.1 ht₂
  -- A character of `C` other than the dominant one has the edge of the dominant character of `C'`.
  have key : ∀ t (ht : t ∈ restrictRows c.supp M), t ≠ d → ∃ hd' : d' ∈ restrictRows c'.supp M,
      edge ⟨c, ⟨t, ht⟩⟩ = edge ⟨c', ⟨d', hd'⟩⟩ := by
    intro t ht htd
    obtain ⟨r, hr, hrt⟩ := mem_restrictRows.1 ht
    have hrd' : c'.supp.domRestrict r = d' := (corollary1 M hcc hd hr).resolve_left fun h₁ => htd (hrt.symm.trans h₁)
    have hd' : d' ∈ restrictRows c'.supp M := mem_restrictRows.2 ⟨r, hr, hrd'⟩
    refine ⟨hd', ?_⟩
    by_contra hne
    obtain ⟨σ, hσ, hσr⟩ := h.exists_side ⟨c, ⟨t, ht⟩⟩
    obtain ⟨σ', hσ', hσr'⟩ := h.exists_side ⟨c', ⟨d', hd'⟩⟩
    obtain ⟨x, hx⟩ := hv ⟨c, ⟨t, ht⟩⟩ rfl
    obtain ⟨x', hx'⟩ := hv' ⟨c', ⟨d', hd'⟩⟩ rfl
    have hadj : T.Adj v x := by
      have := h.edge_mem ⟨c, ⟨t, ht⟩⟩
      rwa [hx] at this
    have hadj' : T.Adj v x' := by
      have := h.edge_mem ⟨c', ⟨d', hd'⟩⟩
      rwa [hx'] at this
    have hs : IsCut T s(v, x) σ := hx ▸ hσ
    have hs' : IsCut T s(v, x') σ' := hx' ▸ hσ'
    have hr₁ : σ (φ ⟨r, hr⟩) = true := by
      rw [hσr]; exact charValue_mk_iff.2 hrt
    have hr₂ : σ' (φ ⟨r, hr⟩) = true := by
      rw [hσr']; exact charValue_mk_iff.2 hrd'
    have hv₁ : σ v ≠ σ (φ ⟨r, hr⟩) := fun heq =>
      hv₀ ⟨c, ⟨t, ht⟩⟩ rfl ⟨r, hr⟩ (charValue_mk_iff.2 hrt) (by rw [hx]; exact hs.sameSide_of_eq hconn hadj heq.symm)
    have hv₂ : σ' v ≠ σ' (φ ⟨r, hr⟩) := fun heq =>
      hv₀' ⟨c', ⟨d', hd'⟩⟩ rfl ⟨r, hr⟩ (charValue_mk_iff.2 hrd') (by rw [hx']; exact hs'.sameSide_of_eq hconn hadj' heq.symm)
    have h₁ : σ v ≠ σ x := hs.ne_self hadj
    have h₂ : σ' v ≠ σ' x' := hs'.ne_self hadj'
    have h₃ : σ v = σ x' := hσ.eq_of_ne hadj' (by rw [hx]; intro heq; rw [hx, hx'] at hne; exact hne heq.symm)
    have h₄ : σ' v = σ' x := hσ'.eq_of_ne hadj (by rw [hx']; intro heq; rw [hx, hx'] at hne; exact hne heq)
    exact IsCut.not_fourth hconn hσ hσ' (h.edge_mem _) (h.edge_mem _) hne (a := σ v) (b := σ' v) (x := v) (y := x') (z := x)
      (w := φ ⟨r, hr⟩) ⟨rfl, rfl⟩ ⟨h₃.symm, nb h₂⟩ ⟨nb h₁, h₄.symm⟩ ⟨nb hv₁, nb hv₂⟩
  obtain ⟨hd₁, he₁⟩ := key t₁ ht₁M ht₁d
  obtain ⟨hd₂, he₂⟩ := key t₂ ht₂M ht₂d
  have hk : (⟨c, ⟨t₁, ht₁M⟩⟩ : SuperChar M) ≠ ⟨c, ⟨t₂, ht₂M⟩⟩ := fun heq => ht (by
    have := eq_of_heq (Sigma.mk.inj_iff.1 heq).2
    exact congrArg Subtype.val this)
  exact h.edge_ne hk rfl hc (he₁.trans he₂.symm)

end TBar

end Gusfield2007
