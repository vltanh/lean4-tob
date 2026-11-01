module

public import External.GusfieldEtAl2004.ReducedExists

/-!
# The reduced galled tree with no given ancestral sequence

See the `README.md` of this directory. Gusfield et al. 2007 work with `G(M)`, and no ancestral sequence, at lines 180 and 381: "When there is a galled-tree for `M`, there is a reduced galled-tree for `M`", citing Gusfield, Eddhu, Langley 2004 and Gusfield 2005. The first treats a known ancestral sequence
(`exists_isReducedGalledTree`), and calls the other case a "future paper"; the second wasn't read. This module proves the unrooted form by the proof of `exists_isReducedGalledTree`, with the root moved.

A galled tree for `M` with ancestral sequence `S₀` needn't be reduced for `G(M)`, for `G_{S₀}(M)` can have more edges: on `M = {01, 10, 11}`, `S₀ = 00`, it needs a gall, while `G(M)` has none. So the new ancestral sequence is a row of `M`, for which the two graphs agree. A row at the recombination node of a gall needn't serve: on the rows `0000, 1000, 1100, 0010, 0011, 1111` the
four sites are one component, and with the root `1111` no row can be removed to leave two chains of flipped sites (a check by hand, not in Lean). So:

* `exists_leaf_avoiding`: some leaf isn't below the recombination node of any gall with an incompatibility. Going down from the root, at the coalescent node of such a gall, leave the gall by an edge to a row with a state pair other than those of the coalescent and recombination nodes. That edge isn't at the
  recombination node, by Lemma 2.1 of the source.
* `exists_turned`: a gall can be rooted at any of its nodes other than the recombination node, by turning round the arcs of the path to that node. The cycle has the same arcs, and the crossover of the recombination node doesn't change.
* The gluing of `exists_reduced_of_pieces` does the rest.
-/

@[expose] public noncomputable section

open scoped Classical

namespace GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {ι V E : Type*}

/-! ### Turning round an arc out of the root -/

section Turn

variable {κ V' E' : Type*} [Finite V']

omit [Finite V'] in
theorem tgt_ne_root' (P : Network κ V' E') (e : E') : P.tgt e ≠ P.root := fun h => (P.root_iff P.root).2 rfl e h

/-- The network with an arc out of the root turned round. Its target, which has no other arc into it, is the new root, and the old root keeps its other arcs. -/
def turnRoot (P : Network κ V' E') (a : E') (h₁ : P.src a = P.root) (h₂ : ∀ f, P.tgt f = P.tgt a → f = a) : Network κ V' E' where
  src e := if e = a then P.tgt a else P.src e
  tgt e := if e = a then P.root else P.tgt e
  root := P.tgt a
  site := P.site
  label := P.label
  simple e f h₃ h₄ := by
    by_cases he : e = a
    · by_cases hf : f = a
      · rw [he, hf]
      · simp only [he, hf, ite_true, ite_false] at h₄
        exact absurd h₄.symm (tgt_ne_root' P f)
    · by_cases hf : f = a
      · simp only [he, hf, ite_true, ite_false] at h₄
        exact absurd h₄ (tgt_ne_root' P e)
      · simp only [he, hf, ite_false] at h₃ h₄
        exact P.simple e f h₃ h₄
  acyclic := by
    obtain ⟨ρ, hρ⟩ := P.exists_rank
    refine acyclic_of_rank (fun v => if v = P.tgt a then 0 else if v = P.root then 1 else ρ v + 2) fun e => ?_
    have hrootne : P.root ≠ P.tgt a := (tgt_ne_root' P a).symm
    by_cases he : e = a
    · simp only [he, ite_true, hrootne, ite_false]
      omega
    · have hte : P.tgt e ≠ P.tgt a := fun h => he (h₂ e h)
      simp only [he, ite_false, hte, tgt_ne_root' P e]
      by_cases hs : P.src e = P.tgt a
      · simp only [hs, ite_true]
        omega
      · by_cases hs' : P.src e = P.root
        · simp only [hs', hrootne, ite_false, ite_true]
          omega
        · simp only [hs, hs', ite_false]
          have := hρ e
          omega
  root_iff v := by
    constructor
    · intro h
      by_contra hne
      by_cases hv : v = P.root
      · exact h a (by simp [hv])
      · have hex : ∃ g, P.tgt g = v := by
          by_contra hno
          push Not at hno
          exact hv ((P.root_iff v).1 hno)
        obtain ⟨g, rfl⟩ := hex
        have hga : g ≠ a := fun h' => hne (by rw [h'])
        exact h g (by simp [hga])
    · rintro rfl e he
      by_cases hea : e = a
      · simp only [hea, ite_true] at he
        exact tgt_ne_root' P a he.symm
      · simp only [hea, ite_false] at he
        exact hea (h₂ e he)
  inDegree_le_two e f g h₃ h₄ := by
    by_cases he : e = a
    · by_cases hf : f = a
      · exact Or.inl (by rw [he, hf])
      · simp only [he, hf, ite_true, ite_false] at h₃
        exact absurd h₃.symm (tgt_ne_root' P f)
    · by_cases hf : f = a
      · simp only [he, hf, ite_true, ite_false] at h₃
        exact absurd h₃ (tgt_ne_root' P e)
      · by_cases hg : g = a
        · simp only [hf, hg, ite_true, ite_false] at h₄
          exact absurd h₄ (tgt_ne_root' P f)
        · simp only [he, hf, hg, ite_false] at h₃ h₄
          exact P.inDegree_le_two e f g h₃ h₄
  site_not_recomb i f h := by
    by_cases hs : P.site i = a
    · by_cases hf : f = a
      · rw [hf, hs]
      · simp only [hs, hf, ite_true, ite_false] at h
        exact absurd h (tgt_ne_root' P f)
    · by_cases hf : f = a
      · simp only [hs, hf, ite_true, ite_false] at h
        exact absurd h.symm (tgt_ne_root' P _)
      · simp only [hs, hf, ite_false] at h
        exact P.site_not_recomb i f h
  label_tree e he i := by
    by_cases hea : e = a
    · subst hea
      have h := P.label_tree e h₂ i
      rw [h₁] at h
      simp only [ite_true]
      by_cases hs : P.site i = e
      · simp only [hs, ite_true] at h ⊢
        rw [h]
        simp
      · simp only [hs, ite_false] at h ⊢
        exact h.symm
    · have huniq : ∀ f, P.tgt f = P.tgt e → f = e := by
        intro f hf
        have hfa : f ≠ a := fun h' => hea (h₂ e (by rw [← hf, h']))
        exact he f (by simp [hfa, hea, hf])
      simp only [hea, ite_false]
      exact P.label_tree e huniq i
  label_recomb e f hef h i := by
    by_cases he : e = a
    · by_cases hf : f = a
      · exact absurd (he.trans hf.symm) hef
      · simp only [he, hf, ite_true, ite_false] at h
        exact absurd h.symm (tgt_ne_root' P f)
    · by_cases hf : f = a
      · simp only [he, hf, ite_true, ite_false] at h
        exact absurd h (tgt_ne_root' P e)
      · simp only [he, hf, ite_false] at h ⊢
        exact P.label_recomb e f hef h i

variable {P : Network κ V' E'} {a : E'} {h₁ : P.src a = P.root} {h₂ : ∀ f, P.tgt f = P.tgt a → f = a}

theorem turnRoot_src {e : E'} (he : e ≠ a) : (turnRoot P a h₁ h₂).src e = P.src e := by simp [turnRoot, he]

theorem turnRoot_tgt {e : E'} (he : e ≠ a) : (turnRoot P a h₁ h₂).tgt e = P.tgt e := by simp [turnRoot, he]

theorem turnRoot_isPath {l : List E'} : ∀ {u v : V'}, a ∉ l → P.IsPath u v l → (turnRoot P a h₁ h₂).IsPath u v l := by
  induction l with
  | nil => exact fun _ h => h
  | cons e l ih =>
    intro u v ha h
    have hne : e ≠ a := fun h' => ha (by simp [h'])
    exact ⟨(turnRoot_src hne).trans h.1, by rw [turnRoot_tgt hne]; exact ih (fun h' => ha (by simp [h'])) h.2⟩

/-- A recombination node of the turned network has the same two arcs in. -/
theorem turnRoot_isRecomb {x : V'} (h : (turnRoot P a h₁ h₂).IsRecomb x) : P.IsRecomb x ∧ ∀ e, (turnRoot P a h₁ h₂).tgt e = x → e ≠ a ∧ P.tgt e = x := by
  obtain ⟨e, f, hef, he, hf⟩ := h
  have hne : ∀ {e f : E'}, e ≠ f → (turnRoot P a h₁ h₂).tgt e = (turnRoot P a h₁ h₂).tgt f → e ≠ a := by
    rintro e f hef htt rfl
    have hfa : f ≠ e := hef.symm
    rw [turnRoot_tgt hfa] at htt
    simp only [turnRoot, ite_true] at htt
    exact tgt_ne_root' P f htt.symm
  have hea : e ≠ a := hne hef (he.trans hf.symm)
  have hfa : f ≠ a := hne hef.symm (hf.trans he.symm)
  refine ⟨⟨e, f, hef, (turnRoot_tgt hea).symm.trans he, (turnRoot_tgt hfa).symm.trans hf⟩, fun g hg => ?_⟩
  have hga : g ≠ a := by
    by_cases hge : g = e
    · rwa [hge]
    · exact hne hge (hg.trans he.symm)
  exact ⟨hga, (turnRoot_tgt hga).symm.trans hg⟩

theorem turnRoot_obeys [LinearOrder κ] {c : Crossover} (h : P.Obeys c) : (turnRoot P a h₁ h₂).Obeys c := by
  rw [obeys_iff] at h ⊢
  intro x hx
  have ⟨hr, hall⟩ := turnRoot_isRecomb hx
  obtain ⟨e, f, hef, he, hf, hrec⟩ := h x hr
  obtain ⟨he', hf'⟩ : e ≠ a ∧ f ≠ a := by
    constructor
    · rintro rfl
      exact hef (h₂ f (by rw [hf, he])).symm
    · rintro rfl
      exact hef (h₂ e (by rw [he, hf]))
  refine ⟨e, f, hef, (turnRoot_tgt he').trans he, (turnRoot_tgt hf').trans hf, ?_⟩
  rw [turnRoot_src he', turnRoot_src hf']
  exact hrec

/-- **Rooting at another node.** Along a path from the root whose arcs have no other arc into their targets, the arcs can be turned round, to root the network at the end of the path, with the same labels and the same recombination nodes. -/
theorem exists_turned [LinearOrder κ] (P : Network κ V' E') {c : List E'} : ∀ {u : V'}, P.IsPath P.root u c → (∀ e ∈ c, ∀ f, P.tgt f = P.tgt e → f = e) →
    ∃ P' : Network κ V' E', P'.root = u ∧ P'.label = P.label ∧ (∀ c', P.Obeys c' → P'.Obeys c') ∧ ∀ x, P'.IsRecomb x → P.IsRecomb x := by
  induction c generalizing P with
  | nil => exact fun h _ => ⟨P, h, rfl, fun _ h' => h', fun _ h' => h'⟩
  | cons a c ih =>
    intro u hp huniq
    have h₁ : P.src a = P.root := hp.1
    have h₂ : ∀ f, P.tgt f = P.tgt a → f = a := huniq a (by simp)
    have hnot : a ∉ c := (IsPath.notMem_of_split (p₁ := []) hp).2
    have hp' : (turnRoot P a h₁ h₂).IsPath (turnRoot P a h₁ h₂).root u c := turnRoot_isPath hnot hp.2
    have huniq' : ∀ e ∈ c, ∀ f, (turnRoot P a h₁ h₂).tgt f = (turnRoot P a h₁ h₂).tgt e → f = e := by
      intro e he f hf
      have hea : e ≠ a := fun h' => hnot (h' ▸ he)
      rw [turnRoot_tgt hea] at hf
      by_cases hfa : f = a
      · subst hfa
        simp only [turnRoot, ite_true] at hf
        exact absurd hf.symm (tgt_ne_root' P e)
      · rw [turnRoot_tgt hfa] at hf
        exact huniq e (by simp [he]) f hf
    obtain ⟨P', h₃, h₄, h₅, h₆⟩ := ih (turnRoot P a h₁ h₂) hp' huniq'
    exact ⟨P', h₃, h₄, fun c' h' => h₅ c' (turnRoot_obeys h'), fun x hx => (turnRoot_isRecomb (h₆ x hx)).1⟩

end Turn

/-! ### A leaf that avoids the recombination nodes -/

section Avoid

variable {N : Network ι V E} [Finite V] {w x : V} {p q : List E}

omit [Finite V] in
/-- Two recombination cycles of a galled tree with a node in common are one. -/
theorem IsGalledTree.eq_of_mem (hG : IsGalledTree N) {Q Q' : Set E} (hQ : N.IsCycle Q) (hQ' : N.IsCycle Q') {v : V} (hv : v ∈ N.blobVerts Q) (hv' : v ∈ N.blobVerts Q') : Q' = Q := by
  by_contra hne
  exact Set.disjoint_left.1 ((hG Q hQ).2 Q' hQ' hne) hv hv'

/-- An arc that has a target with another arc in is on the recombination cycle of that other arc, in a galled tree. -/
theorem IsGalledTree.mem_of_tgt_eq (hG : IsGalledTree N) {Q : Set E} (hQ : N.IsCycle Q) {f g : E} (hg : g ∈ Q) (ht : N.tgt f = N.tgt g) : f ∈ Q := by
  by_cases hfg : f = g
  · rwa [hfg]
  · obtain ⟨Q', hQ', hf', hg'⟩ := exists_isCycle_of_tgt_eq hfg ht
    have heq := hG.eq_of_inter hQ hQ' ⟨g, hg, hg'⟩
    rwa [heq] at hf'

/-- A recombination node on a gall is the recombination node of the gall. -/
theorem IsGalledTree.eq_of_isRecomb (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {y : V} (hy : y ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (hr : N.IsRecomb y) : y = x := by
  have hQ : N.IsCycle {e | e ∈ p ∨ e ∈ q} := ⟨w, x, p, q, hc, rfl⟩
  obtain ⟨w', p', q', hc'⟩ := exists_isCycleOn_of_isRecomb hr
  have hQ' : N.IsCycle {e | e ∈ p' ∨ e ∈ q'} := ⟨w', y, p', q', hc', rfl⟩
  obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc'
  have heq := hG.eq_of_mem hQ hQ' hy (Or.inr ⟨a, Or.inl ha, hax⟩)
  exact cycle_recomb_eq hc' hc heq

omit [Finite V] in
/-- The coalescent node reaches all the nodes of its cycle. -/
theorem coalescent_reach_of_mem (hc : N.IsCycleOn w x p q) {v : V} (hv : v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) : N.Reach w v := by
  rcases hv with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · exact cycle_reach_src hc he
  · exact (cycle_reach_src hc he).trans (reach_src_tgt e)

variable {M : Finset (ι → Bool)}

/-- A recombination cycle with an incompatibility on it. -/
def HasConflict (N : Network ι V E) (M : Finset (ι → Bool)) (Q : Set E) : Prop := ∃ i j, N.site i ∈ Q ∧ N.site j ∈ Q ∧ Incompatible M i j

/-- A recombination node above the target of an arc, other than the target, is above the source. If the arc isn't the one on the path, both are on a gall at the target, and the recombination node is above its coalescent node. -/
theorem reach_src_of_reach_tgt (hG : IsGalledTree N) {f : E} {y : V} (hy : N.IsRecomb y) (hreach : N.Reach y (N.tgt f)) (hne : y ≠ N.tgt f) : N.Reach y (N.src f) := by
  rcases Relation.ReflTransGen.cases_tail hreach with h | ⟨z, hz, g, hgs, hgt⟩
  · exact absurd h.symm hne
  by_cases hgf : g = f
  · rw [← hgs, hgf] at hz
    exact hz
  · obtain ⟨Q, ⟨w', x', p', q', hc', rfl⟩, hg', hf'⟩ := exists_isCycle_of_tgt_eq hgf hgt
    have hxt : N.tgt f = x' := by
      refine hG.eq_of_isRecomb hc' (Or.inr ⟨f, hf', rfl⟩) ⟨g, f, hgf, hgt, rfl⟩
    have hyQ : y ∉ N.blobVerts {e | e ∈ p' ∨ e ∈ q'} := fun hm => hne ((hG.eq_of_isRecomb hc' hm hy).trans hxt.symm)
    have h₁ := reach_coalescent_of_reach_mem hG hc' hyQ (Or.inl ⟨g, hg', hgs⟩) hz
    exact h₁.trans (coalescent_reach_of_mem hc' (Or.inl ⟨f, hf', rfl⟩))

/-- The two conditions for going down: no recombination node of a gall with an incompatibility is above the node, and the node is on such a gall only as its coalescent node. -/
def Clean (N : Network ι V E) (M : Finset (ι → Bool)) (v : V) : Prop :=
  (∀ w x p q, N.IsCycleOn w x p q → HasConflict N M {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x v) ∧
    ∀ w x p q, N.IsCycleOn w x p q → HasConflict N M {e | e ∈ p ∨ e ∈ q} → v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q} → v = w

/-- An arc on no gall with an incompatibility, from a node with no recombination node of such a gall above it, goes to a clean node. -/
theorem clean_tgt (hG : IsGalledTree N) {f : E} (hA : ∀ w x p q, N.IsCycleOn w x p q → HasConflict N M {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x (N.src f))
    (hH : ∀ w x p q, N.IsCycleOn w x p q → HasConflict N M {e | e ∈ p ∨ e ∈ q} → f ∉ {e | e ∈ p ∨ e ∈ q}) : Clean N M (N.tgt f) := by
  refine ⟨fun w x p q hc hconf hr => ?_, fun w x p q hc hconf hm => ?_⟩
  · by_cases hxt : x = N.tgt f
    · obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc
      exact hH w x p q hc hconf (hG.mem_of_tgt_eq ⟨w, x, p, q, hc, rfl⟩ (Or.inl ha) (hax.trans hxt).symm)
    · exact hA w x p q hc hconf (reach_src_of_reach_tgt hG hc.1 hr hxt)
  · by_contra hne
    obtain ⟨g, hg, hgt⟩ := exists_arc_of_mem hc hm hne
    exact hH w x p q hc hconf (hG.mem_of_tgt_eq ⟨w, x, p, q, hc, rfl⟩ hg hgt.symm)

/-- At the coalescent node of a gall with an incompatibility, there's an arc off the gall, from a node of the gall other than the recombination node: to a row with a state pair other than those of the coalescent and recombination nodes. Lemma 2.1 of the source says that such a row isn't below the recombination node. -/
theorem exists_exit (hG : IsGalledTree N) (hD : N.Derives M) (hc : N.IsCycleOn w x p q) (hconf : HasConflict N M {e | e ∈ p ∨ e ∈ q}) :
    ∃ f, N.src f ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q} ∧ N.src f ≠ x ∧ f ∉ {e | e ∈ p ∨ e ∈ q} := by
  obtain ⟨i, j, hi, hj, hij⟩ := hconf
  have hpair : ∀ p₁ p₂ q₁ q₂ : Bool, ∃ a b : Bool, (a ≠ p₁ ∨ b ≠ p₂) ∧ (a ≠ q₁ ∨ b ≠ q₂) := by decide
  obtain ⟨a, b, hax, haw⟩ := hpair (N.label x i) (N.label x j) (N.label w i) (N.label w j)
  obtain ⟨r, hr, h₁, h₂⟩ := hij a b
  obtain ⟨y, hy, rfl⟩ := hD.surjOn hr
  have hreach : N.Reach w y := by
    rcases haw with h | h
    · have hne : N.label y i ≠ N.label N.root i := by
        rw [h₁, ← label_coalescent hc hi]
        exact h
      exact (cycle_reach_src hc hi).trans ((reach_src_tgt _).trans (N.reach_of_label_ne hne))
    · have hne : N.label y j ≠ N.label N.root j := by
        rw [h₂, ← label_coalescent hc hj]
        exact h
      exact (cycle_reach_src hc hj).trans ((reach_src_tgt _).trans (N.reach_of_label_ne hne))
  obtain ⟨l, hl⟩ := hreach.exists_isPath
  obtain ⟨b', p₁, p₂, -, -, hp₂, hb, hf⟩ := hl.exists_last (fun v => v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (coalescent_mem hc)
  have hbx : b' ≠ x := by
    rintro rfl
    rcases hax with h | h
    · exact h (h₁.symm.trans (label_of_reach hG hc hp₂.reach hi))
    · exact h (h₂.symm.trans (label_of_reach hG hc hp₂.reach hj))
  cases p₂ with
  | nil =>
    exfalso
    have hby : b' = y := hp₂
    rcases Relation.ReflTransGen.cases_head (cycle_reach_of_mem hc hb) with h | ⟨z, ⟨e, he, -⟩, -⟩
    · exact hbx h
    · exact hy e (he.trans hby)
  | cons f p₃ =>
    have hsf : N.src f = b' := hp₂.1
    refine ⟨f, hsf ▸ hb, hsf ▸ hbx, fun hfQ => hf f (by simp) (Or.inr ⟨f, hfQ, rfl⟩)⟩

/-- **A row off the recombination nodes.** Some leaf isn't below the recombination node of any gall with an incompatibility: going down from the root, at the coalescent node of such a gall leave it before its recombination node (`exists_exit`), and elsewhere take any arc. -/
theorem exists_leaf_avoiding (hG : IsGalledTree N) (hD : N.Derives M) :
    ∃ l, N.IsLeaf l ∧ ∀ w x p q, N.IsCycleOn w x p q → HasConflict N M {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x l := by
  have key : ∀ v, Clean N M v → ∃ l, N.IsLeaf l ∧ ∀ w x p q, N.IsCycleOn w x p q → HasConflict N M {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x l := by
    intro v
    induction v using N.wellFounded_transGen_swap.induction with
    | _ v ih =>
      rintro ⟨ha, hb⟩
      by_cases hleaf : N.IsLeaf v
      · exact ⟨v, hleaf, ha⟩
      by_cases hw : ∃ x p q, N.IsCycleOn v x p q ∧ HasConflict N M {e | e ∈ p ∨ e ∈ q}
      · obtain ⟨x, p, q, hc, hconf⟩ := hw
        obtain ⟨f, hfm, hfx, hfQ⟩ := exists_exit hG hD hc hconf
        have hQ : N.IsCycle {e | e ∈ p ∨ e ∈ q} := ⟨v, x, p, q, hc, rfl⟩
        refine ih _ (Relation.TransGen.tail' (coalescent_reach_of_mem hc hfm) ⟨f, rfl, rfl⟩) (clean_tgt hG (fun w₁ x₁ p₁ q₁ hc₁ hconf₁ hr => ?_) fun w₁ x₁ p₁ q₁ hc₁ hconf₁ hf => ?_)
        · by_cases hx₁ : x₁ ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}
          · have hxx := hG.eq_of_isRecomb hc hx₁ hc₁.1
            subst hxx
            exact hfx (Reach.antisymm (cycle_reach_of_mem hc hfm) hr)
          · exact ha w₁ x₁ p₁ q₁ hc₁ hconf₁ (reach_coalescent_of_reach_mem hG hc hx₁ hfm hr)
        · have heq := hG.eq_of_mem hQ ⟨w₁, x₁, p₁, q₁, hc₁, rfl⟩ hfm (Or.inl ⟨f, hf, rfl⟩)
          exact hfQ (heq ▸ hf)
      · obtain ⟨f, hf⟩ : ∃ f, N.src f = v := by
          by_contra hno
          push Not at hno
          exact hleaf hno
        subst hf
        refine ih _ (Relation.TransGen.single ⟨f, rfl, rfl⟩) (clean_tgt hG ha fun w₁ x₁ p₁ q₁ hc₁ hconf₁ hfm => ?_)
        have hvw := hb w₁ x₁ p₁ q₁ hc₁ hconf₁ (Or.inl ⟨f, hfm, rfl⟩)
        rw [← hvw] at hc₁
        exact hw ⟨x₁, p₁, q₁, hc₁, hconf₁⟩
  refine key N.root ⟨fun w x p q hc _ hr => ?_, fun w x p q hc _ hm => ?_⟩
  · have hx := N.eq_root_of_reach hr
    exact N.not_isRecomb_root (hx ▸ hc.1)
  · by_contra hne
    obtain ⟨g, -, hg⟩ := exists_arc_of_mem hc hm hne
    exact (N.root_iff N.root).2 rfl g hg

/-- States are constant along a path off a gall (Lemma 2.1 of the source). -/
theorem label_along (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {s : ι} (hs : N.site s ∈ {e | e ∈ p ∨ e ∈ q}) {l : List E} : ∀ {b y : V}, N.IsPath b y l →
    (∀ f ∈ l, N.tgt f ∉ N.blobVerts {e | e ∈ p ∨ e ∈ q}) → N.label y s = N.label b s := by
  induction l with
  | nil =>
    intro b y h _
    rw [show b = y from h]
  | cons f l ih =>
    intro b y h hoff
    rw [ih h.2 fun g hg => hoff g (by simp [hg]), label_tgt_of_notMem hG hc (hoff f (by simp)) hs, h.1]

/-- A node not below the recombination node of a gall has the states on the gall of another node of the gall. -/
theorem exists_attach (hG : IsGalledTree N) (hc : N.IsCycleOn w x p q) {y : V} (hy : ¬ N.Reach x y) :
    ∃ u ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}, u ≠ x ∧ ∀ s, N.site s ∈ {e | e ∈ p ∨ e ∈ q} → N.label y s = N.label u s := by
  by_cases hw : N.Reach w y
  · obtain ⟨l, hl⟩ := hw.exists_isPath
    obtain ⟨b, p₁, p₂, -, -, hp₂, hb, hf⟩ := hl.exists_last (fun v => v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) (coalescent_mem hc)
    refine ⟨b, hb, ?_, fun s hs => label_along hG hc hs hp₂ hf⟩
    rintro rfl
    exact hy hp₂.reach
  · refine ⟨w, coalescent_mem hc, ?_, fun s hs => ?_⟩
    · rintro rfl
      exact hc.ne_nil hc.2.1.eq_nil_of_self
    · by_contra hne
      have hne' : N.label y s ≠ N.label N.root s := by rwa [← label_coalescent hc hs]
      exact hw ((cycle_reach_src hc hs).trans ((reach_src_tgt _).trans (N.reach_of_label_ne hne')))

end Avoid

/-! ### The network of a component, rooted at a row -/

section PieceAt

variable {N : Network ι V E} [Finite V] {w x : V} {p q : List E} {L : Finset (ι → Bool)}

/-- A path on the arcs of a gall is a path of the gall alone. -/
theorem gallNet_path {hG : IsGalledTree N} {hc : N.IsCycleOn w x p q} {κ : Set ι} {hκ : ∀ i ∈ κ, N.site i ∈ {e | e ∈ p ∨ e ∈ q}} {u : V} (hu : u ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}) {c : List E} :
    ∀ {y : V} (hy : y ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}), N.IsPath y u c → (∀ e ∈ c, e ∈ {e | e ∈ p ∨ e ∈ q}) →
      ∃ c' : List {e // e ∈ {e | e ∈ p ∨ e ∈ q}}, (gallNet hG hc κ hκ).IsPath ⟨y, hy⟩ ⟨u, hu⟩ c' ∧ ∀ e' ∈ c', e'.1 ∈ c := by
  induction c with
  | nil =>
    intro y hy h _
    obtain rfl : y = u := h
    exact ⟨[], rfl, by simp⟩
  | cons e c ih =>
    intro y hy h hall
    obtain ⟨c', h₁, h₂⟩ := ih (Or.inr ⟨e, hall e (by simp), rfl⟩) h.2 fun g hg => hall g (by simp [hg])
    refine ⟨⟨e, hall e (by simp)⟩ :: c', ⟨Subtype.ext h.1, h₁⟩, fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · simp
    · simp [h₂ e' he']

/-- **The network of a non-trivial component, rooted at the states of a row.** As `exists_gall_piece`, for a node `y` that isn't below the recombination node of the gall: its states on the gall are those of a node `u` of the gall, other than the recombination node (`exists_attach`), and the gall is rooted at `u` (`exists_turned`). -/
theorem exists_gall_piece_at [LinearOrder ι] (hG : IsGalledTree N) (hL : ∀ r ∈ L, ∃ v, N.label v = r) (C : Cent (incompatGraph L)) {y : V}
    (hy : ∀ w x p q, N.IsCycleOn w x p q → HasConflict N L {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x y) :
    ∃ (a b : ℕ) (P : Network C.1.supp (Fin a) (Fin b)), (∀ c, N.Obeys c → P.Obeys c) ∧ P.ancestral = C.1.supp.domRestrict (N.label y) ∧
      P.Derives ((restrictRows C.1.supp L).erase (C.1.supp.domRestrict (N.label y))) ∧ P.recombCount ≤ 1 := by
  obtain ⟨i₀, j₀, hi₀, hadj⟩ := Cent.exists_adj C
  obtain ⟨Q, hQ, hsi, hsj⟩ := exists_isCycle_of_incompatible N hL hadj
  have hj₀ : j₀ ∈ C.1.supp := (SimpleGraph.ConnectedComponent.eq.2 hadj.reachable).symm.trans hi₀
  have hκ : ∀ s ∈ C.1.supp, N.site s ∈ Q := fun s hs => theorem2_4 hG hQ hL hsi (SimpleGraph.ConnectedComponent.exact (hi₀.trans hs.symm))
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  have : Finite {e // e ∈ {e | e ∈ p ∨ e ∈ q}} := Set.Finite.to_subtype (Set.Finite.subset ((List.finite_toSet p).union (List.finite_toSet q)) fun e he => he)
  obtain ⟨u, hu, hux, hyu⟩ := exists_attach hG hc (hy w x p q hc ⟨i₀, j₀, hsi, hsj, hadj⟩)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = gallNet hG hc C.1.supp hκ := ⟨_, rfl⟩
  -- the path to `u`
  obtain ⟨c, hcp, hcQ⟩ : ∃ c, N.IsPath w u c ∧ ∀ e ∈ c, e ∈ {e | e ∈ p ∨ e ∈ q} := by
    rcases cycle_mem_cases hc hu with h | ⟨c, d, hp, -, hcv⟩ | ⟨c, d, hq, -, hcv⟩
    · exact absurd h hux
    · exact ⟨c, hcv, fun e he => Or.inl (by rw [hp]; exact List.mem_append_left _ he)⟩
    · exact ⟨c, hcv, fun e he => Or.inr (by rw [hq]; exact List.mem_append_left _ he)⟩
  obtain ⟨c', hc'p, hc'm⟩ := gallNet_path (hG := hG) (hc := hc) (κ := C.1.supp) (hκ := hκ) hu (coalescent_mem hc) hcp hcQ
  have huniq : ∀ e ∈ c', ∀ f, P₀.tgt f = P₀.tgt e → f = e := by
    intro e he f hf
    subst hP₀
    by_contra hne
    have hrec : (gallNet hG hc C.1.supp hκ).IsRecomb ((gallNet hG hc C.1.supp hκ).tgt e) := ⟨f, e, hne, hf, rfl⟩
    have htx : N.tgt e.1 = x := gallNet_isRecomb hrec
    have h₁ : N.Reach x u := htx ▸ hcp.reach_tgt_of_mem (hc'm e he)
    exact hux (Reach.antisymm (cycle_reach_of_mem hc hu) h₁)
  obtain ⟨P₁, hr₁, hl₁, ho₁, hrec₁⟩ := exists_turned P₀ (u := ⟨u, hu⟩) (by rw [hP₀]; exact hc'p) huniq
  have hlabel : ∀ (v : {v // v ∈ N.blobVerts {e | e ∈ p ∨ e ∈ q}}) (s : C.1.supp), P₁.label v s = N.label v.1 s.1 := fun v s => by
    rw [hl₁, hP₀]
    rfl
  obtain ⟨T, hT⟩ : ∃ T, T = (restrictRows C.1.supp L).erase (C.1.supp.domRestrict (N.label y)) := ⟨_, rfl⟩
  have hanc : ∀ r : T, ∃ v, P₁.label v = r.1 := by
    rintro ⟨r, hr⟩
    rw [hT] at hr
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hr)
    obtain ⟨z, rfl⟩ := hL ρ hρ
    obtain ⟨v, hv, hzv⟩ := exists_mem_label_eq hG hc z
    refine ⟨⟨v, hv⟩, ?_⟩
    funext s
    rw [hlabel]
    exact (hzv s.1 (hκ s.1 s.2)).symm
  choose anchor hanchor using hanc
  have hroot : P₁.label P₁.root = C.1.supp.domRestrict (N.label y) := by
    funext s
    rw [hr₁, hlabel]
    exact (hyu s.1 (hκ s.1 s.2)).symm
  have hs : ∀ s : C.1.supp, ∃ r ∈ T, r s ≠ P₁.label P₁.root s := by
    intro s
    obtain ⟨k, hk⟩ := exists_incompatible_of_nontrivial C.2 s.2
    obtain ⟨r, hr, h₁, -⟩ := hk (!N.label y s.1) true
    have hne : (!N.label y s.1) ≠ N.label y s.1 := by cases N.label y s.1 <;> simp
    have hrs : C.1.supp.domRestrict r s = !N.label y s.1 := h₁
    refine ⟨C.1.supp.domRestrict r, ?_, ?_⟩
    · rw [hT]
      refine Finset.mem_erase.2 ⟨fun h' => ?_, Finset.mem_image_of_mem _ hr⟩
      have := congrFun h' s
      rw [hrs] at this
      exact hne this
    · rw [hroot, hrs]
      exact hne
  have hTne : T.Nonempty := by
    obtain ⟨r, hr, -⟩ := hs ⟨i₀, hi₀⟩
    exact ⟨r, hr⟩
  obtain ⟨a, b, P, h₁, h₂, h₃, h₄⟩ := P₁.exists_trim hTne hanchor hs
  refine ⟨a, b, P, fun c' hc' => h₁ c' (ho₁ c' (by rw [hP₀]; exact gallNet_obeys hG hc hκ hL hi₀ hj₀ hadj hc')), h₃.trans hroot, hT ▸ h₂, h₄.trans ?_⟩
  refine Finite.card_le_one_iff_subsingleton.2 ⟨fun v v' => ?_⟩
  have hx : ∀ z : {z // P₁.IsRecomb z ∧ P₁.Kept anchor z}, z.1.1 = x := fun z => by
    have := hrec₁ _ z.2.1
    rw [hP₀] at this
    exact gallNet_isRecomb this
  exact Subtype.ext (Subtype.ext ((hx v).trans (hx v').symm))

end PieceAt

/-! ### The results -/

section Results

variable [LinearOrder ι] [Finite ι] {N : Network ι V E} [Finite V] {M : Finset (ι → Bool)}

/-- **Gusfield et al. 2007, line 180** (`g:reduced_exists`). "When there is a galled-tree for `M`, there is a reduced galled-tree for `M`", for `G(M)`: with some ancestral sequence, a row of `M`, in the same crossover model. The standing assumption of Gusfield et al. 2007 on the columns is the hypothesis.
With a known ancestral sequence, this is Corollary 5.1 of Gusfield, Eddhu, Langley 2004 (`exists_isReducedGalledTree`). The head of this file says how this form is proved, and that the second reference of line 180 wasn't read. -/
theorem exists_isReducedGalledTree_incompatGraph (hG : IsGalledTree N) (hD : N.Derives M) (hC : NoConstantColumn M) {c : Crossover} (hc : N.Obeys c) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ IsReducedGalledTree N' (incompatGraph M) := by
  obtain ⟨y, hleaf, hy⟩ := exists_leaf_avoiding hG hD
  have hyM : N.label y ∈ M := Finset.mem_coe.1 (hD.mapsTo hleaf)
  have heq : addRow M (N.label y) = M := addRow_eq_of_mem hyM
  have hL : ∀ r ∈ addRow M (N.label y), ∃ v, N.label v = r := fun r hr => hD.displays r (heq ▸ hr)
  have hy' : ∀ w x p q, N.IsCycleOn w x p q → HasConflict N (addRow M (N.label y)) {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x y := by
    rw [heq]
    exact hy
  have hC' : NoConstantColumn (addRow M (N.label y)) := hC.addRow _
  by_cases hne : ∃ r ∈ addRow M (N.label y), r ≠ N.label y
  · choose a b P hob hanc hder hrec using fun C : Cent (incompatGraph (addRow M (N.label y))) => exists_gall_piece_at hG hL C hy'
    obtain ⟨a', b', N', h₁, h₂, -, h₄⟩ := exists_reduced_of_pieces c hC' hne P (fun C => hob C c hc) hanc hder hrec
    rw [heq] at h₄
    exact ⟨a', b', N', h₁, h₂, h₄⟩
  · push Not at hne
    have hι : IsEmpty ι := ⟨fun i => by
      obtain ⟨r, hr, r', hr', hrr⟩ := hC i
      rw [hne r (by rw [heq]; exact hr), hne r' (by rw [heq]; exact hr')] at hrr
      exact hrr rfl⟩
    obtain ⟨a', b', N', hr, hd, -, -⟩ := Gusfield1991.exists_network_of_no_conflict M (N.label y) hD.nonempty hC' (fun i => hι.elim i)
    have hinj := Network.tgt_injective_of_no_recomb hr
    have hcyc : ∀ Q, ¬ N'.IsCycle Q := Network.not_isCycle_of_tgt_injective hinj
    exact ⟨a', b', N', Network.obeys_of_tgt_injective hinj c, hd, fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q)⟩

/-- **Gusfield et al. 2007, line 381** (`g:line381_of_galled`). "The answer is yes when `M` can be derived on a galled-tree, even if the galled-tree must only use single-crossover recombinations, but any competing phylogenetic network is allowed to use multiple-crossovers": if `M` can be derived on a galled tree in the model `c`, then it is min decomposable, for `c` and for multiple crossovers. -/
theorem minDecomposable_of_isGalledTree (hG : IsGalledTree N) (hD : N.Derives M) (hC : NoConstantColumn M) {c : Crossover} (hc : N.Obeys c) :
    MinDecomposable c M ∧ MinDecomposable .multiple M := by
  obtain ⟨a, b, N', h₁, h₂, h₄⟩ := exists_isReducedGalledTree_incompatGraph hG hD hC hc
  exact line381 h₄ h₂ h₁

/-- **Gusfield et al. 2007, line 381**, the value (`g:line381_of_galled`): if `M` can be derived on a galled tree in the model `c`, then `R(M)`, for `c` and for multiple crossovers, is the number of non-trivial components of `G(M)`. -/
theorem R_eq_card_cent (hG : IsGalledTree N) (hD : N.Derives M) (hC : NoConstantColumn M) {c : Crossover} (hc : N.Obeys c) :
    R c M = Nat.card (Cent (incompatGraph M)) ∧ R .multiple M = Nat.card (Cent (incompatGraph M)) := by
  obtain ⟨a, b, N', h₁, h₂, h₄⟩ := exists_isReducedGalledTree_incompatGraph hG hD hC hc
  obtain ⟨h₅, h₆⟩ := reducedGalledTree_recombCount_eq_R h₄ h₂ h₁
  have h₇ := h₄.recombCount_eq_incompatGraph h₂
  exact ⟨h₅.symm.trans h₇, h₆.symm.trans h₇⟩

end Results

end GusfieldEtAl2004
