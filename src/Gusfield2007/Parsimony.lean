module

public import Gusfield2007.Histories
public import Gusfield2007.NetworkOps

/-!
# Gusfield et al. 2007, Section 4.1: trees with back and recurrent mutations, as networks

"An occurrence of back-mutation or recurrent-mutation of a site `i` in a sequence `S` can be modeled as a two-crossover recombination between `S` and some appropriate sequence" (line 358). This module has
both directions of that correspondence, and re-rooting, which Corollary 3 and line 411 use:

* `MutationTree.parsimonyScore_le_of_displays`: a tree in which every row labels a node bounds the parsimony score;
* `MutationTree.exists_reroot`: the root of a tree can be moved to any node, at the same cost;
* `Network.exists_mutationTree`: a network of recombinations that model mutations gives a tree;
* `MutationTree.exists_gen`, `Gen.exists_preNet`: a tree gives a history (`Gen`, in the model of one changed site) of mutations and of recombinations modelling them, and a history gives a network.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

universe u v w

namespace MutationTree

variable {ι : Type u} {V : Type v} {E : Type w} (T : MutationTree ι V E)

/-- The arc relation on nodes. -/
def Arc (a b : V) : Prop := ∃ e, T.src e = a ∧ T.tgt e = b

/-- A directed path, weakly. -/
def Reach : V → V → Prop := Relation.ReflTransGen T.Arc

/-- Every node is reached from the root. -/
theorem reach_root [Finite V] (v : V) : T.Reach T.root v := by
  have : IsTrans V (Relation.TransGen T.Arc) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen T.Arc) := ⟨T.acyclic⟩
  induction v using (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen T.Arc)).induction with
  | _ v ih =>
    by_cases hv : ∀ e, T.tgt e ≠ v
    · rw [(T.root_iff v).1 hv]
      exact Relation.ReflTransGen.refl
    · push Not at hv
      obtain ⟨e, he⟩ := hv
      have ha : T.Arc (T.src e) v := ⟨e, rfl, he⟩
      exact (ih _ (Relation.TransGen.single ha)).tail ha

/-- The cost, as a number of pairs of an arc and a site. -/
theorem mutationCount_eq_card [Finite E] [Finite ι] :
    T.mutationCount = Nat.card {p : E × ι // T.label (T.src p.1) p.2 ≠ T.label (T.tgt p.1) p.2} := by
  have : Fintype E := Fintype.ofFinite E
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun (e : E) (i : ι) => T.label (T.src e) i ≠ T.label (T.tgt e) i),
    mutationCount, finsum_eq_sum_of_fintype, Nat.card_sigma]
  rfl

/-- Transport along bijections. -/
def map {V' : Type*} {E' : Type*} (eV : V ≃ V') (eE : E ≃ E') : MutationTree ι V' E' where
  src e := eV (T.src (eE.symm e))
  tgt e := eV (T.tgt (eE.symm e))
  root := eV T.root
  label v := T.label (eV.symm v)
  acyclic v h := by
    have key : ∀ {a b}, Relation.TransGen (fun a b => ∃ e, eV (T.src (eE.symm e)) = a ∧ eV (T.tgt (eE.symm e)) = b) a b →
        Relation.TransGen (fun a b => ∃ e, T.src e = a ∧ T.tgt e = b) (eV.symm a) (eV.symm b) := by
      intro a b h
      refine Relation.TransGen.lift eV.symm ?_ _ _ h
      rintro a b ⟨e, rfl, rfl⟩
      exact ⟨eE.symm e, by simp, by simp⟩
    exact T.acyclic _ (key h)
  root_iff v := by
    have := T.root_iff (eV.symm v)
    constructor
    · intro h
      have h' : ∀ e, T.tgt e ≠ eV.symm v := fun e he => h (eE e) (by simp [he])
      rw [← this.1 h']
      simp
    · rintro rfl e he
      exact ((T.root_iff T.root).2 rfl) (eE.symm e) (eV.injective he)
  inDegree_le_one e f h := eE.symm.injective (T.inDegree_le_one _ _ (eV.injective h))

theorem mutationCount_map {V' : Type*} {E' : Type*} (eV : V ≃ V') (eE : E ≃ E') : (T.map eV eE).mutationCount = T.mutationCount := by
  unfold mutationCount map
  simp only [Equiv.symm_apply_apply]
  exact finsum_comp_equiv eE.symm (f := fun e => Set.ncard {i | T.label (T.src e) i ≠ T.label (T.tgt e) i})

section Trim

variable {M : Finset (ι → Bool)} (anchor : M → V)

/-- `T` with only the nodes that reach a chosen node for each row, and a pendant leaf for each row, as in `Network.trim`. -/
def trim [Finite V] (hroot : ∃ r, T.Reach T.root (anchor r)) :
    MutationTree ι ({v // ∃ r, T.Reach v (anchor r)} ⊕ M) ({e // ∃ r, T.Reach (T.tgt e) (anchor r)} ⊕ M) where
  src := Sum.elim (fun e => .inl ⟨T.src e.1, by
    obtain ⟨r, hr⟩ := e.2
    exact ⟨r, Relation.ReflTransGen.head ⟨e.1, rfl, rfl⟩ hr⟩⟩) (fun r => .inl ⟨anchor r, r, Relation.ReflTransGen.refl⟩)
  tgt := Sum.elim (fun e => .inl ⟨T.tgt e.1, e.2⟩) .inr
  root := .inl ⟨T.root, hroot⟩
  label := Sum.elim (fun v => T.label v.1) (fun r => r.1)
  acyclic := by
    obtain ⟨ρ, hρ⟩ := exists_rank T.Arc T.acyclic
    refine Network.acyclic_of_rank (Sum.elim (fun v => ρ v.1) (fun r => ρ (anchor r) + 1)) ?_
    rintro (e | r)
    · exact hρ _ _ ⟨e.1, rfl, rfl⟩
    · exact Nat.lt_succ_self _
  root_iff := by
    rintro (v | r)
    · constructor
      · intro h
        have : ∀ e, T.tgt e ≠ v.1 := fun e he =>
          h (.inl ⟨e, he ▸ v.2⟩) (by simp only [Sum.elim_inl, Sum.inl.injEq]; exact Subtype.ext he)
        have := (T.root_iff v.1).1 this
        exact congrArg Sum.inl (Subtype.ext this)
      · intro h
        have hv : v.1 = T.root := congrArg Subtype.val (Sum.inl.inj h)
        rintro (e | r) he
        · exact (T.root_iff _).2 hv e.1 (congrArg Subtype.val (Sum.inl.inj he))
        · exact absurd he (by simp)
    · constructor
      · intro h
        exact absurd rfl (h (.inr r))
      · intro h
        simp at h
  inDegree_le_one := by
    rintro (e | r) (f | r') h <;> simp only [Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢
    · exact Subtype.ext (T.inDegree_le_one _ _ (congrArg Subtype.val h))
    · exact h

variable {T anchor}

/-- **A tree in which every row labels a node** (`g:tree_trim`). There's a tree on `Fin a`, `Fin b` deriving exactly the rows, with the same root label and no higher cost. -/
theorem exists_fin_of_displays [Finite V] [Finite E] [Finite ι] (T : MutationTree ι V E) (hM : M.Nonempty) (hd : ∀ r ∈ M, ∃ v, T.label v = r) :
    ∃ (a b : ℕ) (T' : MutationTree ι (Fin a) (Fin b)), T'.label T'.root = T.label T.root ∧
      Set.BijOn T'.label {v | ∀ e, T'.src e ≠ v} (M : Set (ι → Bool)) ∧ T'.mutationCount ≤ T.mutationCount := by
  choose anchor hanchor using fun r : M => hd r.1 r.2
  have hroot : ∃ r, T.Reach T.root (anchor r) := by
    obtain ⟨r, hr⟩ := hM
    exact ⟨⟨r, hr⟩, T.reach_root _⟩
  set T₁ := T.trim anchor hroot with hT₁
  have hleaf : ∀ x, (∀ e, T₁.src e ≠ x) ↔ ∃ r, x = .inr r := by
    rintro (v | r)
    · constructor
      · intro h
        exfalso
        obtain ⟨r, hr⟩ := v.2
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h' | h'
        · exact h (.inr r) (congrArg Sum.inl (Subtype.ext h'))
        · obtain ⟨b, hb, hr'⟩ := Relation.TransGen.head'_iff.1 h'
          obtain ⟨e, he, rfl⟩ := hb
          exact h (.inl ⟨e, r, hr'⟩) (congrArg Sum.inl (Subtype.ext he))
      · rintro ⟨r, hr⟩
        simp at hr
    · refine ⟨fun _ => ⟨r, rfl⟩, fun _ => ?_⟩
      rintro (e | r') h <;> simp [hT₁, trim] at h
  have hbij : Set.BijOn T₁.label {v | ∀ e, T₁.src e ≠ v} (M : Set (ι → Bool)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨r, rfl⟩ := (hleaf x).1 hx
      exact r.2
    · intro x hx y hy hxy
      obtain ⟨r, rfl⟩ := (hleaf x).1 hx
      obtain ⟨r', rfl⟩ := (hleaf y).1 hy
      exact congrArg Sum.inr (Subtype.ext hxy)
    · intro r hr
      exact ⟨.inr ⟨r, hr⟩, (hleaf _).2 ⟨_, rfl⟩, rfl⟩
  have hcost : T₁.mutationCount ≤ T.mutationCount := by
    rw [mutationCount_eq_card, mutationCount_eq_card]
    have hne : ∀ (r : M) (i : ι), ¬ (T₁.label (T₁.src (.inr r)) i ≠ T₁.label (T₁.tgt (.inr r)) i) := fun r i h =>
      h (congrFun (hanchor r) i)
    refine Nat.card_le_card_of_injective (fun p => match p with
      | ⟨(.inl e, i), h⟩ => ⟨(e.1, i), h⟩
      | ⟨(.inr r, i), h⟩ => absurd h (hne r i)) ?_
    rintro ⟨⟨e | r, i⟩, hi⟩ ⟨⟨e' | r', i'⟩, hi'⟩ h
    · have h' := congrArg Subtype.val h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨h₁, rfl⟩ := h'
      obtain rfl : e = e' := Subtype.ext h₁
      rfl
    · exact absurd hi' (hne r' i')
    · exact absurd hi (hne r i)
    · exact absurd hi (hne r i)
  obtain ⟨a, ⟨eV⟩⟩ := Finite.exists_equiv_fin ({v // ∃ r, T.Reach v (anchor r)} ⊕ M)
  obtain ⟨b, ⟨eE⟩⟩ := Finite.exists_equiv_fin ({e // ∃ r, T.Reach (T.tgt e) (anchor r)} ⊕ M)
  refine ⟨a, b, T₁.map eV eE, ?_, ⟨?_, ?_, ?_⟩, (mutationCount_map T₁ eV eE).le.trans hcost⟩
  · change T₁.label (eV.symm (eV T₁.root)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · intro v hv
    refine hbij.mapsTo (x := eV.symm v) fun e he => hv (eE e) ?_
    change eV (T₁.src (eE.symm (eE e))) = v
    rw [Equiv.symm_apply_apply, he, Equiv.apply_symm_apply]
  · intro v hv w hw hvw
    refine eV.symm.injective (hbij.injOn (x₁ := eV.symm v) (x₂ := eV.symm w) ?_ ?_ hvw)
    · refine fun e he => hv (eE e) ?_
      change eV (T₁.src (eE.symm (eE e))) = v
      rw [Equiv.symm_apply_apply, he, Equiv.apply_symm_apply]
    · refine fun e he => hw (eE e) ?_
      change eV (T₁.src (eE.symm (eE e))) = w
      rw [Equiv.symm_apply_apply, he, Equiv.apply_symm_apply]
  · intro r hr
    obtain ⟨x, hx, hxr⟩ := hbij.surjOn hr
    refine ⟨eV x, fun e he => hx (eE.symm e) (eV.injective he), ?_⟩
    change T₁.label (eV.symm (eV x)) = r
    rw [Equiv.symm_apply_apply, hxr]

end Trim

/-- **A tree bounds the parsimony score** (`g:tree_bound`). -/
theorem parsimonyScore_le_of_displays {M : Finset (ι → Bool)} [Finite V] [Finite E] [Finite ι] (T : MutationTree ι V E) (hM : M.Nonempty) (hd : ∀ r ∈ M, ∃ v, T.label v = r) :
    parsimonyScore (T.label T.root) M ≤ T.mutationCount := by
  obtain ⟨a, b, T', h₁, h₂, h₃⟩ := exists_fin_of_displays T hM hd
  have h : parsimonyScore (T.label T.root) M ≤ T'.mutationCount := Nat.sInf_le ⟨a, b, T', h₁, h₂, rfl⟩
  exact h.trans h₃

/-! ### Moving the root -/

/-- `T` with the arc `e` out of the root reversed. The root is now the target of `e`. -/
def reverseRoot (e : E) (he : T.src e = T.root) : MutationTree ι V E where
  src g := if g = e then T.tgt e else T.src g
  tgt g := if g = e then T.root else T.tgt g
  root := T.tgt e
  label := T.label
  acyclic := by
    have hne : T.tgt e ≠ T.root := fun h => (T.root_iff T.root).2 rfl e h
    refine Network.acyclic_of_add_arc (r := fun a b => ∃ g, g ≠ e ∧ T.src g = a ∧ T.tgt g = b) (y := T.tgt e) (x := T.root) ?_ ?_ ?_
    · intro a h
      refine T.acyclic a (Relation.TransGen.mono ?_ _ _ h)
      rintro a b ⟨g, -, h₁, h₂⟩
      exact ⟨g, h₁, h₂⟩
    · rintro a b ⟨g, h₁, h₂⟩
      by_cases hg : g = e
      · subst hg
        simp only [ite_true] at h₁ h₂
        exact Or.inr ⟨h₁.symm, h₂.symm⟩
      · rw [ite_eq_right hg] at h₁ h₂
        exact Or.inl ⟨g, hg, h₁, h₂⟩
    · intro h
      rcases Relation.ReflTransGen.cases_tail h with h' | ⟨d, -, g, hg, -, h₂⟩
      · exact hne h'
      · exact hg (T.inDegree_le_one _ _ h₂)
  root_iff v := by
    constructor
    · intro h
      by_contra hv
      by_cases hroot : v = T.root
      · exact h e (by rw [ite_eq_left rfl, hroot])
      · obtain ⟨g, hg⟩ : ∃ g, T.tgt g = v := by
          by_contra hno
          push Not at hno
          exact hroot ((T.root_iff v).1 hno)
        have hge : g ≠ e := fun h' => hv (by rw [← hg, h'])
        exact h g (by rw [ite_eq_right hge, hg])
    · rintro rfl g hg
      by_cases hge : g = e
      · rw [ite_eq_left hge] at hg
        exact (T.root_iff T.root).2 rfl e hg.symm
      · rw [ite_eq_right hge] at hg
        exact hge (T.inDegree_le_one _ _ hg)
  inDegree_le_one g k h := by
    by_cases hg : g = e <;> by_cases hk : k = e
    · rw [hg, hk]
    · rw [ite_eq_left hg, ite_eq_right hk] at h
      exact absurd h.symm ((T.root_iff T.root).2 rfl k)
    · rw [ite_eq_right hg, ite_eq_left hk] at h
      exact absurd h ((T.root_iff T.root).2 rfl g)
    · rw [ite_eq_right hg, ite_eq_right hk] at h
      exact T.inDegree_le_one _ _ h

theorem mutationCount_reverseRoot (e : E) (he : T.src e = T.root) : (T.reverseRoot e he).mutationCount = T.mutationCount := by
  unfold mutationCount
  refine finsum_congr fun g => ?_
  by_cases hg : g = e
  · subst hg
    change Set.ncard {i | T.label (if g = g then T.tgt g else T.src g) i ≠ T.label (if g = g then T.root else T.tgt g) i} = _
    simp only [ite_true, ← he, ne_comm]
  · change Set.ncard {i | T.label (if g = e then T.tgt e else T.src g) i ≠ T.label (if g = e then T.root else T.tgt g) i} = _
    rw [ite_eq_right hg, ite_eq_right hg]

/-- A list of arcs is a directed path. -/
def IsPath : V → V → List E → Prop
  | u, v, [] => u = v
  | u, v, e :: p => T.src e = u ∧ IsPath (T.tgt e) v p

/-- A path reaches any source of its arcs. -/
theorem IsPath.reach_src {T : MutationTree ι V E} {v : V} {e : E} : ∀ {l : List E} {u : V}, T.IsPath u v l → e ∈ l → T.Reach u (T.src e)
  | [], _, _, h => absurd h (List.not_mem_nil)
  | g :: l, u, hp, h => by
    obtain ⟨rfl, hp'⟩ := hp
    rcases List.mem_cons.1 h with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨g, rfl, rfl⟩ (IsPath.reach_src hp' h)

theorem exists_isPath {T : MutationTree ι V E} {u v : V} (h : T.Reach u v) : ∃ l, T.IsPath u v l := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | head ha _ ih =>
    obtain ⟨e, rfl, rfl⟩ := ha
    obtain ⟨l, hl⟩ := ih
    exact ⟨e :: l, rfl, hl⟩

/-- **Re-rooting** (`g:reroot`). The root of a tree can be moved to any node, at the same cost: "the parsimony score doesn't change on re-rooting", as it depends only on the undirected tree. -/
theorem exists_reroot [Finite V] (T : MutationTree ι V E) (v : V) :
    ∃ T' : MutationTree ι V E, T'.root = v ∧ T'.label = T.label ∧ T'.mutationCount = T.mutationCount := by
  obtain ⟨l, hl⟩ := exists_isPath (T.reach_root v)
  induction l generalizing T with
  | nil => exact ⟨T, hl, rfl, rfl⟩
  | cons e l ih =>
    obtain ⟨he, hp⟩ := hl
    have hnot : e ∉ l := fun hmem => by
      have hr := IsPath.reach_src hp hmem
      rw [he] at hr
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h' | h'
      · exact (T.root_iff T.root).2 rfl e h'.symm
      · obtain ⟨d, -, g, -, hg⟩ := Relation.TransGen.tail'_iff.1 h'
        exact (T.root_iff T.root).2 rfl g hg
    have hpath : ∀ (l : List E) (u : V), e ∉ l → T.IsPath u v l → (T.reverseRoot e he).IsPath u v l := by
      intro l
      induction l with
      | nil => exact fun _ _ h => h
      | cons g l ih' =>
        intro u hu hp'
        have hge : g ≠ e := fun h => hu (h ▸ List.mem_cons_self)
        obtain ⟨h₁, h₂⟩ := hp'
        refine ⟨?_, ?_⟩
        · change (if g = e then T.tgt e else T.src g) = u
          rw [ite_eq_right hge, h₁]
        · have : (T.reverseRoot e he).tgt g = T.tgt g := ite_eq_right hge
          rw [this]
          exact ih' _ (fun h => hu (List.mem_cons_of_mem _ h)) h₂
    obtain ⟨T', h₁, h₂, h₃⟩ := ih (T.reverseRoot e he) (hpath l _ hnot hp)
    exact ⟨T', h₁, h₂, h₃.trans (mutationCount_reverseRoot T e he)⟩

/-- **The score at a row** (`g:parsimony_row`). Among all ancestral sequences, a row of `M` has the least parsimony score, if a tree exists for `S`: re-root an optimal tree at the row. -/
theorem parsimonyScore_row_le {M : Finset (ι → Bool)} {S r : ι → Bool} [Finite ι] (hr : r ∈ M) (hne : {k | ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), T.label T.root = S ∧
    Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧ T.mutationCount = k}.Nonempty) :
    parsimonyScore r M ≤ parsimonyScore S M := by
  obtain ⟨a, b, T, -, hbij, hcount⟩ := Nat.sInf_mem hne
  obtain ⟨v, -, hv⟩ := hbij.surjOn hr
  obtain ⟨T', h₁, h₂, h₃⟩ := T.exists_reroot v
  have h := parsimonyScore_le_of_displays T' (M := M) ⟨r, hr⟩ fun r' hr' => by
    obtain ⟨w, -, hw⟩ := hbij.surjOn hr'
    exact ⟨w, by rw [h₂, hw]⟩
  have hroot : T'.label T'.root = r := by rw [h₁, h₂, hv]
  rw [hroot, h₃] at h
  exact h.trans hcount.le

end MutationTree

/-! ### From a network to a tree -/

namespace Network

variable {ι : Type u} [LinearOrder ι] {V : Type v} {E : Type w}

/-- **A network of recombinations that model mutations gives a tree** (`g:network_tree`). At each recombination node, remove the arc from the parent that supplies the changed site. Each site costs one mutation on its arc, and each recombination node at most one more: "each mutation beyond the first
at a site is one recombination modelling it" (lines 358, 511). -/
theorem exists_mutationTree [Finite V] [Finite E] [Finite ι] (N : Network ι V E) (hc : N.Obeys .pointwise) :
    ∃ (E' : Type w) (_ : Finite E') (T : MutationTree ι V E'), T.root = N.root ∧ T.label = N.label ∧ T.mutationCount ≤ Nat.card ι + N.recombCount := by
  have hc' : ∀ x : {x // N.IsRecomb x}, ∃ e f, e ≠ f ∧ N.tgt e = x.1 ∧ N.tgt f = x.1 ∧ ∃ j, ∀ i, N.label x.1 i = if i = j then N.label (N.src f) i else N.label (N.src e) i :=
    fun x => hc x.1 x.2
  choose e f hef he hf j hj using hc'
  have hret : ∀ x y, e x ≠ f y := by
    intro x y h
    have hxy : x = y := Subtype.ext ((he x).symm.trans ((congrArg N.tgt h).trans (hf y)))
    subst hxy
    exact hef x h
  have hin : ∀ (g : {g // ∀ x, g ≠ f x}) (x : {x // N.IsRecomb x}), N.tgt g.1 = x.1 → g.1 = e x := by
    intro g x hg
    rcases eq_or_eq_of_tgt (hef x) ((he x).trans (hf x).symm) (hg.trans (he x).symm) with h | h
    · exact h
    · exact absurd h (g.2 x)
  have hinj : ∀ g k : {g // ∀ x, g ≠ f x}, N.tgt g.1 = N.tgt k.1 → g = k := by
    intro g k h
    by_cases hr : N.IsRecomb (N.tgt k.1)
    · exact Subtype.ext ((hin g ⟨_, hr⟩ h).trans (hin k ⟨_, hr⟩ rfl).symm)
    · exact Subtype.ext (eq_of_not_isRecomb hr h)
  let T : MutationTree ι V {g // ∀ x, g ≠ f x} :=
    { src := fun g => N.src g.1
      tgt := fun g => N.tgt g.1
      root := N.root
      label := N.label
      acyclic := fun v h => N.acyclic v (Relation.TransGen.mono (fun _ _ ⟨g, h₁, h₂⟩ => ⟨g.1, h₁, h₂⟩) _ _ h)
      root_iff := fun v => by
        refine ⟨fun h => (N.root_iff v).1 fun k hk => ?_, fun h g => (N.root_iff v).2 h g.1⟩
        by_cases hkf : ∀ x, k ≠ f x
        · exact h ⟨k, hkf⟩ hk
        · push Not at hkf
          obtain ⟨x, rfl⟩ := hkf
          exact h ⟨e x, fun y => hret x y⟩ ((he x).trans ((hf x).symm.trans hk))
      inDegree_le_one := hinj }
  refine ⟨_, inferInstance, T, rfl, rfl, ?_⟩
  rw [MutationTree.mutationCount_eq_card]
  have hcard : Nat.card ι + N.recombCount = Nat.card (ι ⊕ {x // N.IsRecomb x}) := by
    rw [Nat.card_sum]
    rfl
  rw [hcard]
  have hsite : ∀ (g : {g // ∀ x, g ≠ f x}) (i : ι), ¬ N.IsRecomb (N.tgt g.1) → N.label (N.src g.1) i ≠ N.label (N.tgt g.1) i → N.site i = g.1 := by
    intro g i hr hi
    by_contra hs
    have hl := N.label_tree g.1 (fun k hk => eq_of_not_isRecomb hr hk) i
    rw [ite_eq_right hs] at hl
    exact hi hl.symm
  have hjx : ∀ (g : {g // ∀ x, g ≠ f x}) (i : ι) (hr : N.IsRecomb (N.tgt g.1)), N.label (N.src g.1) i ≠ N.label (N.tgt g.1) i → i = j ⟨_, hr⟩ := by
    intro g i hr hi
    by_contra hne
    have hl := hj ⟨_, hr⟩ i
    rw [ite_eq_right hne, ← hin g ⟨_, hr⟩ rfl] at hl
    exact hi hl.symm
  refine Nat.card_le_card_of_injective (fun p => if h : N.IsRecomb (N.tgt p.1.1.1) then .inr ⟨_, h⟩ else .inl p.1.2) ?_
  rintro ⟨⟨g, i⟩, hi⟩ ⟨⟨g', i'⟩, hi'⟩ h
  by_cases hr : N.IsRecomb (N.tgt g.1) <;> by_cases hr' : N.IsRecomb (N.tgt g'.1)
  · simp only [hr, hr', ↓reduceDIte, Sum.inr.injEq, Subtype.mk.injEq] at h
    obtain rfl := hinj g g' h
    have h₁ := hjx g i hr hi
    have h₂ := hjx g i' hr' hi'
    have h₃ : i = i' := h₁.trans h₂.symm
    subst h₃
    rfl
  · simp [hr, hr'] at h
  · simp [hr, hr'] at h
  · simp only [hr, hr', ↓reduceDIte, Sum.inl.injEq] at h
    subst h
    have h₁ := hsite g i hr hi
    have h₂ := hsite g' i hr' hi'
    obtain rfl : g = g' := Subtype.ext (h₁.symm.trans h₂)
    rfl

end Network

/-! ### From a tree to a network, through a history -/

section History

variable {ι : Type u} [LinearOrder ι]

namespace PreNet

variable {V : Type v} (P : PreNet ι V)

omit [LinearOrder ι] in
theorem recombCount_extend_none [Finite V] (p : V) (h : ι → Bool) (s : ι → Prop) (hs : ∀ j, s j → P.site j = none)
    (hq : ∀ q₀, none = some q₀ → q₀ ≠ p ∧ (∀ j, h j = P.label p j ∨ h j = P.label q₀ j) ∧ ∀ j, ¬ s j)
    (hq' : (none : Option V) = none → ∀ j, h j = if s j then !P.label p j else P.label p j) :
    (P.extend p none h s hs hq hq').recombCount ≤ P.recombCount := by
  have hsub : {x | (P.extend p none h s hs hq hq').par₂ x ≠ none} ⊆ some '' {x | P.par₂ x ≠ none} := by
    rintro (- | v) hx
    · exact absurd rfl hx
    · refine ⟨v, fun h' => hx ?_, rfl⟩
      change (P.par₂ v).map some = none
      rw [h']
      rfl
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  rw [Set.ncard_image_of_injective _ (Option.some_injective _)]
  rfl

omit [LinearOrder ι] in
theorem recombCount_extend_some [Finite V] (p q : V) (h : ι → Bool) (s : ι → Prop) (hs : ∀ j, s j → P.site j = none)
    (hq : ∀ q₀, some q = some q₀ → q₀ ≠ p ∧ (∀ j, h j = P.label p j ∨ h j = P.label q₀ j) ∧ ∀ j, ¬ s j)
    (hq' : some q = none → ∀ j, h j = if s j then !P.label p j else P.label p j) :
    (P.extend p (some q) h s hs hq hq').recombCount ≤ P.recombCount + 1 := by
  have hsub : {x | (P.extend p (some q) h s hs hq hq').par₂ x ≠ none} ⊆ some '' {x | P.par₂ x ≠ none} ∪ {none} := by
    rintro (- | v) hx
    · exact Or.inr rfl
    · refine Or.inl ⟨v, fun h' => hx ?_, rfl⟩
      change (P.par₂ v).map some = none
      rw [h']
      rfl
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_union_le _ _).trans ?_)
  rw [Set.ncard_image_of_injective _ (Option.some_injective _), Set.ncard_singleton]
  rfl

end PreNet

namespace Gen

variable {S : ι → Bool} {A : Finset (ι → Bool)} {U : Set ι} {k : ℕ}

/-- **A history is a `PreNet`** (`g:history_prenet`). -/
theorem exists_preNet (h : Gen .pointwise S A U k) :
    ∃ (V : Type) (_ : Finite V) (P : PreNet ι V), P.label P.root = S ∧ (∀ s ∈ A, ∃ v, P.label v = s) ∧ (∀ i, i ∈ U ↔ ∃ v, P.site i = some v) ∧
      (∀ x p q, P.par x = some p → P.par₂ x = some q → Recombinant .pointwise (P.label q) (P.label p) (P.label x)) ∧ P.recombCount ≤ k := by
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
    obtain ⟨j, hj⟩ := hm
    obtain rfl : q' = fun i => if i = j then t i else s i := funext hj
    obtain ⟨V, _, P, h₁, h₂, h₃, h₄, h₅⟩ := ih
    by_cases hst : s = t
    · subst hst
      have hsame : (fun i => if i = j then s i else s i) = s := by
        funext i
        simp
      refine ⟨V, inferInstance, P, h₁, ?_, h₃, h₄, h₅.trans (Nat.le_succ k)⟩
      intro s' hs'
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · rw [hsame]
        exact h₂ s hs
      · exact h₂ s' hs'
    · obtain ⟨v, rfl⟩ := h₂ s hs
      obtain ⟨w, rfl⟩ := h₂ t ht
      have hvw : v ≠ w := fun h' => hst (by rw [h'])
      refine ⟨Option V, inferInstance, P.extend w (some v) (fun i => if i = j then P.label w i else P.label v i) (fun _ => False) (fun _ h' => h'.elim) ?_ (by simp), h₁, ?_, ?_, ?_,
        (P.recombCount_extend_some _ _ _ _ _ _ _).trans (Nat.add_le_add_right h₅ 1)⟩
      · rintro q₀ hq₀
        obtain rfl := Option.some_inj.1 hq₀
        refine ⟨hvw, fun i => ?_, fun _ h' => h'⟩
        by_cases hi : i = j <;> simp [hi]
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
          exact ⟨j, fun i => rfl⟩
        · simp only [PreNet.extend, Option.map_eq_some_iff] at hp hq
          obtain ⟨p', hp', rfl⟩ := hp
          obtain ⟨q', hq', rfl⟩ := hq
          exact h₄ x p' q' hp' hq'

/-- A history with every site mutated bounds `R_S(M)` in the model of mutations. -/
theorem RS_le [Finite ι] {M : Finset (ι → Bool)} (h : Gen .pointwise S A U k) (hU : ∀ i, i ∈ U) (hMA : ∀ r ∈ M, r ∈ A) (hM : M.Nonempty) (hC : NoConstantColumn M) :
    RS .pointwise S M ≤ k := by
  obtain ⟨V, _, P, h₁, h₂, h₃, h₄, h₅⟩ := h.exists_preNet
  obtain ⟨a, b, N, hc, hd, hS, hcount⟩ := P.exists_network (fun i => (h₃ i).1 (hU i)) h₄ hM hC fun r hr => h₂ r (hMA r hr)
  exact (RS_le_recombCount N hc hd (hS.trans h₁)).trans (hcount.trans h₅)

/-- One more change of a site: a mutation if it's the first, and otherwise a recombination with a sequence that has the other state, the root or the sequence after the first mutation. -/
theorem exists_change [Finite ι] (h : Gen .pointwise S A U k) {s : ι → Bool} (hs : s ∈ A) (i : ι) :
    ∃ A' U' k', Gen .pointwise S A' U' k' ∧ A ⊆ A' ∧ U ⊆ U' ∧ i ∈ U' ∧ (fun j => if j = i then !s j else s j) ∈ A' ∧ k' + U'.ncard = k + U.ncard + 1 := by
  by_cases hi : i ∈ U
  · have : ∃ t ∈ A, t i ≠ s i := by
      obtain ⟨t, ht, hne⟩ := h.exists_ne i hi
      by_cases hsi : s i = S i
      · exact ⟨t, ht, hsi ▸ hne⟩
      · exact ⟨S, h.root_mem, fun h' => hsi h'.symm⟩
    obtain ⟨t, ht, hne⟩ := this
    have hfun : (fun j => if j = i then !s j else s j) = fun j => if j = i then t j else s j := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [↓reduceIte]
        cases h₁ : t j <;> cases h₂ : s j <;> simp_all
      · simp [hj]
    refine ⟨_, U, k + 1, Gen.recomb h hs ht (q := fun j => if j = i then t j else s j) ⟨i, fun _ => rfl⟩, Finset.subset_insert _ _, subset_rfl, hi, ?_, by omega⟩
    rw [hfun]
    exact Finset.mem_insert_self _ _
  · refine ⟨_, insert i U, k, Gen.flip h hs hi (q := fun j => if j = i then !s j else s j) (i := i) ⟨by simp, fun j hj => by simp [hj]⟩, Finset.subset_insert _ _, Set.subset_insert _ _, Set.mem_insert _ _, Finset.mem_insert_self _ _, ?_⟩
    rw [Set.ncard_insert_of_notMem hi (Set.toFinite U)]
    omega

/-- Changes on a set of sites, one at a time. Unlike `Gen.flips`, the sites needn't be new: a change at a site that has already changed is a recombination. -/
theorem exists_changes [Finite ι] (h : Gen .pointwise S A U k) {s : ι → Bool} (hs : s ∈ A) (D : Finset ι) :
    ∃ A' U' k', Gen .pointwise S A' U' k' ∧ A ⊆ A' ∧ U ⊆ U' ∧ (D : Set ι) ⊆ U' ∧ (fun j => if j ∈ D then !s j else s j) ∈ A' ∧ k' + U'.ncard = k + U.ncard + D.card := by
  induction D using Finset.induction_on with
  | empty => exact ⟨A, U, k, h, subset_rfl, subset_rfl, by simp, by simpa using hs, by simp⟩
  | @insert i D hi ih =>
    obtain ⟨A₁, U₁, k₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih
    obtain ⟨A₂, U₂, k₂, h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h₁.exists_change h₅ i
    refine ⟨A₂, U₂, k₂, h₁', h₂.trans h₂', h₃.trans h₃', ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hj) with rfl | hj
      · exact h₄'
      · exact h₃' (h₄ hj)
    · convert h₅' using 2 with j
      by_cases hj : j = i
      · subst hj
        simp [hi]
      · simp [hj]
    · rw [Finset.card_insert_of_notMem hi]
      omega

end Gen

end History

namespace MutationTree

variable {ι : Type u} [LinearOrder ι] [Fintype ι] {V : Type v} {E : Type w} [Finite V] [Finite E]

omit [Finite E] in
/-- **A tree is a history** (`g:tree_history`), for the nodes `W`, closed under taking the parent. Each change on an arc is a mutation if it's the first at its site, and otherwise a recombination that models a back or recurrent mutation (lines 358, 511). -/
theorem exists_gen [Fintype E] (T : MutationTree ι V E) :
    ∀ W : Finset V, T.root ∈ W → (∀ e, T.tgt e ∈ W → T.src e ∈ W) → ∃ A U K, Gen .pointwise (T.label T.root) A U K ∧ (∀ v ∈ W, T.label v ∈ A) ∧
      (∀ e, T.tgt e ∈ W → ∀ i, T.label (T.src e) i ≠ T.label (T.tgt e) i → i ∈ U) ∧
      K + U.ncard = ∑ e with T.tgt e ∈ W, (Finset.univ.filter fun i => T.label (T.src e) i ≠ T.label (T.tgt e) i).card := by
  obtain ⟨rk, hrk⟩ := exists_rank T.Arc T.acyclic
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
    intro hroot hclosed
    by_cases hW : W = {T.root}
    · have hno : ∀ e, T.tgt e ∉ W := fun e he => by
        rw [hW, Finset.mem_singleton] at he
        exact (T.root_iff T.root).2 rfl e he
      refine ⟨{T.label T.root}, ∅, 0, Gen.base, ?_, fun e he => absurd he (hno e), ?_⟩
      · intro v hv
        rw [hW, Finset.mem_singleton] at hv
        rw [hv]
        exact Finset.mem_singleton_self _
      · simp [hno]
    · have hne : (W.erase T.root).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at hempty
        rcases hempty with h | h
        · exact absurd hroot (by simp [h])
        · exact hW h
      obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image (W.erase T.root) rk hne
      obtain ⟨hvroot, hvW⟩ := Finset.mem_erase.1 hv
      obtain ⟨e₀, he₀⟩ : ∃ e, T.tgt e = v := by
        by_contra hno
        push Not at hno
        exact hvroot ((T.root_iff v).1 hno)
      subst he₀
      have hsrcne : ∀ e, T.tgt e ∈ W → T.src e ≠ T.tgt e₀ := by
        rintro e he hsrc
        have hle := hmax (T.tgt e) (Finset.mem_erase.2 ⟨fun h => (T.root_iff T.root).2 rfl e h, he⟩)
        have hlt := hrk _ _ (⟨e, rfl, rfl⟩ : T.Arc (T.src e) (T.tgt e))
        rw [hsrc] at hlt
        omega
      obtain ⟨L, U, K, h₁, h₂, h₃, h₄⟩ := ih (W.erase (T.tgt e₀)) (Finset.erase_ssubset hvW) (Finset.mem_erase.2 ⟨fun h => hvroot h.symm, hroot⟩)
        fun e he => Finset.mem_erase.2 ⟨hsrcne e (Finset.mem_of_mem_erase he), hclosed e (Finset.mem_of_mem_erase he)⟩
      have hsrc₀ : T.src e₀ ∈ W.erase (T.tgt e₀) := Finset.mem_erase.2 ⟨fun h => T.acyclic _ (Relation.TransGen.single ⟨e₀, rfl, h.symm⟩), hclosed e₀ hvW⟩
      set D := Finset.univ.filter fun i => T.label (T.src e₀) i ≠ T.label (T.tgt e₀) i with hD
      obtain ⟨L', U', K', h₁', h₂', h₃', h₄', h₅', h₆'⟩ := h₁.exists_changes (h₂ _ hsrc₀) D
      have hlabel : (fun j => if j ∈ D then !T.label (T.src e₀) j else T.label (T.src e₀) j) = T.label (T.tgt e₀) := by
        funext j
        by_cases hj : j ∈ D
        · have hne' := (Finset.mem_filter.1 hj).2
          rw [ite_eq_left hj]
          cases h₁ : T.label (T.src e₀) j <;> cases h₂ : T.label (T.tgt e₀) j <;> simp_all
        · rw [ite_eq_right hj]
          by_contra hne'
          exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne'⟩)
      rw [hlabel] at h₅'
      refine ⟨L', U', K', h₁', ?_, ?_, ?_⟩
      · intro u hu
        by_cases huv : u = T.tgt e₀
        · rw [huv]
          exact h₅'
        · exact h₂' (h₂ u (Finset.mem_erase.2 ⟨huv, hu⟩))
      · intro e he i hi
        by_cases hev : T.tgt e = T.tgt e₀
        · obtain rfl := T.inDegree_le_one _ _ hev
          exact h₄' (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩))
        · exact h₃' (h₃ e (Finset.mem_erase.2 ⟨hev, he⟩) i hi)
      · have hfilter : (Finset.univ.filter fun e => T.tgt e ∈ W) = insert e₀ (Finset.univ.filter fun e => T.tgt e ∈ W.erase (T.tgt e₀)) := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
          constructor
          · intro he
            by_cases hev : T.tgt e = T.tgt e₀
            · exact Or.inl (T.inDegree_le_one _ _ hev)
            · exact Or.inr ⟨hev, he⟩
          · rintro (rfl | ⟨-, he⟩)
            · exact hvW
            · exact he
        have hnotin : e₀ ∉ Finset.univ.filter fun e => T.tgt e ∈ W.erase (T.tgt e₀) := by simp
        rw [hfilter, Finset.sum_insert hnotin, ← h₄, h₆', ← hD]
        omega

/-- The bridge for Corollary 3, in one direction. -/
theorem card_add_RS_le (T : MutationTree ι V E) {M : Finset (ι → Bool)} (hM : M.Nonempty) (hC : NoConstantColumn M) (hd : ∀ r ∈ M, ∃ v, T.label v = r) :
    Fintype.card ι + RS .pointwise (T.label T.root) M ≤ T.mutationCount := by
  have : Fintype E := Fintype.ofFinite E
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨A, U, K, h₁, h₂, h₃, h₄⟩ := T.exists_gen Finset.univ (Finset.mem_univ _) fun _ _ => Finset.mem_univ _
  have hU : ∀ i, i ∈ U := by
    intro i
    by_contra hi
    have hconst : ∀ v, T.label v i = T.label T.root i := by
      intro v
      have hr := T.reach_root v
      induction hr with
      | refl => rfl
      | tail _ hbc ih =>
        obtain ⟨e, rfl, rfl⟩ := hbc
        rw [← ih]
        by_contra hne
        exact hi (h₃ e (Finset.mem_univ _) i fun h => hne h.symm)
    obtain ⟨r, hr, r', hr', hne⟩ := hC i
    obtain ⟨v, rfl⟩ := hd r hr
    obtain ⟨v', rfl⟩ := hd r' hr'
    exact hne ((hconst v).trans (hconst v').symm)
  have hUcard : U.ncard = Fintype.card ι := by
    rw [Set.eq_univ_of_forall hU, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hRS := h₁.RS_le hU (fun r hr => by
    obtain ⟨v, rfl⟩ := hd r hr
    exact h₂ v (Finset.mem_univ _)) hM hC
  have hcount : ∑ e with T.tgt e ∈ (Finset.univ : Finset V), (Finset.univ.filter fun i => T.label (T.src e) i ≠ T.label (T.tgt e) i).card = T.mutationCount := by
    rw [mutationCount, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr (by simp) fun e _ => ?_
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  rw [← hcount, ← h₄, hUcard]
  omega

end MutationTree

end Gusfield2007
