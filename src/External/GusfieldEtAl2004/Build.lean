module

public import External.GusfieldEtAl2004.Algorithm
public import Mathlib.Data.List.MinMax

/-!
# The reduced galled tree, computed (Gusfield, Eddhu, Langley 2004, Sections 3 to 6)

See the `README.md` of this directory. `Algorithm.lean` decides. This module builds the network from the arrangements of the components, as functions on explicit nodes:

* the rows below a node are its cluster (`GNode.cl`): for a component with sites `C`, `top c` has the rows with a state other than the ancestral sequence's on `C`, and `part c σ` the rows equal to `σ` on `C`, one node of the gall for each;
* a node is below another when its cluster is inside the other's (`Up`), which is the source's ancestry of galls (Section 4) and its placing of the unconflicted sites and the leaves (Section 6) at once: Theorem 2 of Gusfield et al. 2007 says that the clusters are nested or disjoint (`trichotomy`);
* the nodes of a gall are chained as the arrangement says (Section 3.2).

`galledBuild S M` is the function: `none` when there is no galled tree (`galledBuild_isSome_iff`), and otherwise a table of nodes, parents and labels, which is a reduced galled tree (`galledBuild_correct`). Its count is in `BuildCount.lean`.

Departure from the source: its Sections 4 and 6 connect the galls by comparing the numbers of `1`s in columns, and walk the unconflicted sites up from the leaves, with cases, and its Section 7 then checks the result. Here one rule, inclusion of clusters, gives all the parents outside the galls, and the proof shows that no check is needed: Theorem 2 of Gusfield et al. 2007 is the ancestry of the galls. The recombination point isn't read from the bipartition of Lemma 3.1, but tried.
-/

@[expose] public section

namespace GusfieldEtAl2004.Algorithm

variable {m : ℕ}

/-- The nodes: the root, the top of a component (its coalescent node, or the node below the arc of a site alone in its component), a node of a gall for a sequence of the component, and a leaf for a row. -/
inductive GNode (m : ℕ) where
  | root : GNode m
  | top (c : Fin m) : GNode m
  | part (c : Fin m) (σ : Row m) : GNode m
  | leaf (r : Row m) : GNode m

instance : DecidableEq (GNode m)
  | .root, .root => isTrue rfl
  | .top a, .top b => if h : a = b then isTrue (by rw [h]) else isFalse (by simpa using h)
  | .part a σ, .part b τ => if h : a = b then (if h' : σ = τ then isTrue (by rw [h, h']) else isFalse (by simp [h'])) else isFalse (by simp [h])
  | .leaf a, .leaf b => if h : a = b then isTrue (by rw [h]) else isFalse (by simpa using h)
  | .root, .top _ | .root, .part _ _ | .root, .leaf _ | .top _, .root | .top _, .part _ _ | .top _, .leaf _
  | .part _ _, .root | .part _ _, .top _ | .part _ _, .leaf _ | .leaf _, .root | .leaf _, .top _ | .leaf _, .part _ _ => isFalse (by simp)

/-- An arrangement: the row at the recombination node, and the two chains, the second supplying the prefix. -/
abbrev Arr (m : ℕ) := Row m × List (Row m) × List (Row m)

section Core

variable (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m)

/-- The sites of a component. -/
def sitesOf (c : Fin m) : List (Fin m) := (List.finRange m).filter fun k => f k = c

/-- The component has conflicts. -/
def isNT (c : Fin m) : Bool := decide (1 < (sitesOf f c).length)

/-- The row on the sites of a component, and the ancestral sequence elsewhere. -/
def mkRow (c : Fin m) (r : Row m) : Row m := fun i => if f i = c then r i else S i

/-- The sequences of a component other than the ancestral one. -/
def rowsOf (c : Fin m) : List (Row m) := ((M.map (mkRow S f c)).dedup).filter fun σ => σ ≠ S

/-- Which rows are below a node. -/
def GNode.cl : GNode m → Row m → Bool
  | .root, _ => true
  | .top c, r => decide (mkRow S f c r ≠ S)
  | .part c σ, r => decide (mkRow S f c r = σ)
  | .leaf ρ, r => decide (r = ρ)

/-- The order of nodes with one cluster: a node of a gall, then a site alone, then a coalescent node, then a leaf. -/
def GNode.rank : GNode m → ℕ
  | .root => 0
  | .part _ _ => 1
  | .top c => if isNT f c then 3 else 2
  | .leaf _ => 4

/-- A number to break ties. -/
def GNode.idx : GNode m → ℕ
  | .top c => c.val
  | .part c _ => c.val
  | _ => 0

/-- `u` is above `v`, in the order of clusters. -/
def Up (u v : GNode m) : Bool :=
  decide (u ≠ v) && M.all (fun r => !v.cl S f r || u.cl S f r) &&
    (!(M.all fun r => !u.cl S f r || v.cl S f r) || decide (u.rank f < v.rank f) || (decide (u.rank f = v.rank f) && decide (u.idx < v.idx)))

/-- A number that goes up along `Up`. -/
def key (u : GNode m) : ℕ := (M.length - (M.filter (u.cl S f)).length) * (6 * (m + 1)) + u.rank f * (m + 1) + u.idx

/-- The labels of the components. -/
def reps : List (Fin m) := ((List.finRange m).map f).dedup

/-- The nodes that can be parents of a node by clusters. -/
def cands : List (GNode m) := .root :: (reps f).map .top ++ ((reps f).filter (isNT f)).flatMap fun c => (rowsOf S M f c).map (.part c)

/-- The parent of a node by clusters: the lowest node above it. -/
def treePar (v : GNode m) : Option (GNode m) := ((cands S M f).filter fun u => Up S M f u v).argmax (key S M f)

/-- The number of `1`s of a row. -/
def card1 (y : Row m) : ℕ := ((List.finRange m).filter fun i => y i != S i).length

/-- The end of a chain, or the coalescent node. -/
def endNode (c : Fin m) (X : List (Row m)) : GNode m :=
  match X.argmax (card1 S) with
  | some y => .part c y
  | none => .top c

/-- The node before a row on a chain, or the coalescent node. -/
def predNode (c : Fin m) (X : List (Row m)) (σ : Row m) : GNode m := endNode S c (X.filter fun y => card1 S y < card1 S σ)

/-- The parent of a node. -/
def par : GNode m → Option (GNode m)
  | .root => none
  | .part c σ =>
    if σ = (ar c).1 then some (endNode S c (ar c).2.1)
    else if σ ∈ (ar c).2.1 then some (predNode S c (ar c).2.1 σ) else some (predNode S c (ar c).2.2 σ)
  | v => treePar S M f v

/-- The other parent of a node: of the recombination node of a gall. -/
def par₂ : GNode m → Option (GNode m)
  | .part c σ => if σ = (ar c).1 then some (endNode S c (ar c).2.2) else none
  | _ => none

/-- The **arrangement** of a component, the first that the Site-Arrangement Algorithm accepts: the two chains are ordered so that the second supplies the prefix. -/
def arrOf (c : Fin m) : Arr m :=
  match (rowsOf S M f c).find? (fun s => (candidate S (sitesOf f c) (rowsOf S M f c) s).1) with
  | none => (S, [], [])
  | some s =>
    match (filterOps (rowsOf S M f c) fun r => (!(eqOn (sitesOf f c) r s).1, (eqOn (sitesOf f c) r s).2)).1 with
    | [] => (s, [], [])
    | seed :: tl =>
      if (List.range (m + 1)).any (fun n => (recombOk S (sitesOf f c) (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1 (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1 s n).1) then
        (s, (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1, (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1)
      else
        (s, (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1, (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1)

/-- The node below the arc of a site. -/
def siteNode (i : Fin m) : GNode m :=
  if isNT f (f i) then
    match (((ar (f i)).2.1 ++ (ar (f i)).2.2).filter fun y => y i != S i).argmin (card1 S) with
    | some y => .part (f i) y
    | none => .root
  else .top (f i)

/-- The label of a node: on a site alone in its component, whether its arc is above; on a component, the sequence of the gall node above, or the node's own. -/
def label (v : GNode m) (i : Fin m) : Bool :=
  if isNT f (f i) then
    match v with
    | .part c σ => if c = f i then σ i else
      (match (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) with
        | some τ => τ i
        | none => S i)
    | _ =>
      (match (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) with
        | some τ => τ i
        | none => S i)
  else if v = .top (f i) || Up S M f (.top (f i)) v then !S i else S i

end Core

/-! ### The clusters are nested or disjoint -/

section Laminar

open scoped Classical

open Gusfield2007 Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)} {f : Fin m → Fin m}

/-- The components, as labels. -/
def IsLab (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : Prop := ∀ k l, f k = f l ↔ (incompatGraph (addRow M.toFinset S)).Reachable k l

theorem mk_ne_iff {c : Fin m} {r : Row m} : mkRow S f c r ≠ S ↔ ∃ i, f i = c ∧ r i ≠ S i := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    refine h (funext fun i => ?_)
    by_cases hi : f i = c
    · simp only [mkRow, hi, ite_true]
      exact hno i hi
    · simp [mkRow, hi]
  · rintro ⟨i, hi, hri⟩ h
    apply hri
    have := congrFun h i
    simpa [mkRow, hi] using this

theorem mem_rowsOf {c : Fin m} {σ : Row m} : σ ∈ rowsOf S M f c ↔ (∃ r ∈ M, mkRow S f c r = σ) ∧ σ ≠ S := by
  simp [rowsOf]

theorem mk_mk {c : Fin m} {r : Row m} : mkRow S f c (mkRow S f c r) = mkRow S f c r := by
  funext i
  by_cases hi : f i = c <;> simp [mkRow, hi]

/-- **The two components** (Theorem 2 of Gusfield et al. 2007, for `M + S`): the rows off the ancestral sequence on two components are disjoint, or those of one are all at one sequence of the other. -/
theorem trichotomy (hf : IsLab S M f) {k₀ k₀' : Fin m} (hne : f k₀ ≠ f k₀') :
    (∀ r ∈ M, mkRow S f (f k₀) r = S ∨ mkRow S f (f k₀') r = S) ∨ (∃ σ, σ ≠ S ∧ ∀ r ∈ M, mkRow S f (f k₀') r ≠ S → mkRow S f (f k₀) r = σ) ∨ (∃ σ', σ' ≠ S ∧ ∀ r ∈ M, mkRow S f (f k₀) r ≠ S → mkRow S f (f k₀') r = σ') := by
  set G := incompatGraph (addRow M.toFinset S) with hG
  have hmem : ∀ {k k' : Fin m}, f k = f k' ↔ k ∈ (G.connectedComponentMk k').supp := fun {k k'} =>
    (hf k k').trans (SimpleGraph.ConnectedComponent.eq (G := G)).symm
  have hc : G.connectedComponentMk k₀ ≠ G.connectedComponentMk k₀' := fun h => hne ((hf _ _).2 (SimpleGraph.ConnectedComponent.exact h))
  obtain ⟨d, d', hdom⟩ := exists_isDominantFor (addRow M.toFinset S) hc
  have hS : S ∈ addRow M.toFinset S := mem_addRow.2 (Or.inl rfl)
  have hrow : ∀ {r}, r ∈ M → r ∈ addRow M.toFinset S := fun hr => mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr))
  by_cases h₁ : ∀ i (hi : f i = f k₀), S i = d ⟨i, hmem.1 hi⟩
  · by_cases h₂ : ∀ i (hi : f i = f k₀'), S i = d' ⟨i, hmem.1 hi⟩
    · refine Or.inl fun r hr => ?_
      by_contra hno
      push Not at hno
      obtain ⟨i, hi, hri⟩ := mk_ne_iff.1 hno.1
      obtain ⟨i', hi', hri'⟩ := mk_ne_iff.1 hno.2
      rcases hdom ⟨i, hmem.1 hi⟩ ⟨i', hmem.1 hi'⟩ r (hrow hr) with h | h
      · exact hri (h.trans (h₁ i hi).symm)
      · exact hri' (h.trans (h₂ i' hi').symm)
    · -- the ancestral sequence isn't dominant on the second
      push Not at h₂
      obtain ⟨i', hi', hne'⟩ := h₂
      refine Or.inr (Or.inr ⟨fun j => if hj : f j = f k₀' then d' ⟨j, hmem.1 hj⟩ else S j, fun h => hne' ?_, fun r hr hrne => ?_⟩)
      · have := congrFun h i'
        simp only [hi', ↓reduceDIte] at this
        exact this.symm
      · funext j
        by_cases hj : f j = f k₀'
        · obtain ⟨i, hi, hri⟩ := mk_ne_iff.1 hrne
          simp only [mkRow, hj, ite_true, ↓reduceDIte]
          rcases hdom ⟨i, hmem.1 hi⟩ ⟨j, hmem.1 hj⟩ r (hrow hr) with h | h
          · exact absurd (h.trans (h₁ i hi).symm) hri
          · exact h
        · simp [mkRow, hj]
  · push Not at h₁
    obtain ⟨i₁, hi₁, hne₁⟩ := h₁
    refine Or.inr (Or.inl ⟨fun j => if hj : f j = f k₀ then d ⟨j, hmem.1 hj⟩ else S j, fun h => hne₁ ?_, fun r hr hrne => ?_⟩)
    · have := congrFun h i₁
      simp only [hi₁, ↓reduceDIte] at this
      exact this.symm
    · funext j
      by_cases hj : f j = f k₀
      · obtain ⟨i', hi', hri'⟩ := mk_ne_iff.1 hrne
        simp only [mkRow, hj, ite_true, ↓reduceDIte]
        rcases hdom ⟨j, hmem.1 hj⟩ ⟨i', hmem.1 hi'⟩ r (hrow hr) with h | h
        · exact h
        · -- the second is dominated by the ancestral sequence, which isn't dominant on the first
          have hSd := hdom ⟨i₁, hmem.1 hi₁⟩ ⟨i', hmem.1 hi'⟩ S hS
          rcases hSd with h' | h'
          · exact absurd h' hne₁
          · exact absurd (h.trans h'.symm) hri'
      · simp [mkRow, hj]

/-- The nodes of the network. -/
def Valid (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : GNode m → Prop
  | .root => True
  | .top c => ∃ k, f k = c
  | .part c σ => isNT f c = true ∧ σ ∈ rowsOf S M f c
  | .leaf r => r ∈ M

/-- The rows below `u` are below `v`. -/
def SubCl (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (u v : GNode m) : Prop := ∀ r ∈ M, u.cl S f r = true → v.cl S f r = true

theorem SubCl.trans' {u v w : GNode m} (h₁ : SubCl S M f u v) (h₂ : SubCl S M f v w) : SubCl S M f u w := fun r hr h => h₂ r hr (h₁ r hr h)

/-- The order on nodes with one cluster. -/
def Tie (f : Fin m → Fin m) (u v : GNode m) : Prop := u.rank f < v.rank f ∨ (u.rank f = v.rank f ∧ u.idx < v.idx)

theorem up_iff {u v : GNode m} : Up S M f u v = true ↔ u ≠ v ∧ SubCl S M f v u ∧ (SubCl S M f u v → Tie f u v) := by
  have himp : ∀ a b : Bool, ((!a || b) = true) ↔ (a = true → b = true) := by decide
  have hall : ∀ {x y : GNode m}, M.all (fun r => !x.cl S f r || y.cl S f r) = true ↔ SubCl S M f x y := by
    intro x y
    simp only [List.all_eq_true, himp, SubCl]
  simp only [Up, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, hall]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨h₁, h₂, fun h₄ => ?_⟩
    have h₅ : M.all (fun r => !u.cl S f r || v.cl S f r) = true := hall.2 h₄
    rcases h₃ with (h₆ | h₆) | h₆
    · rw [h₅] at h₆
      exact absurd h₆ (by simp)
    · exact Or.inl h₆
    · exact Or.inr h₆
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    by_cases h₄ : SubCl S M f u v
    · rcases h₃ h₄ with h₅ | h₅
      · exact Or.inl (Or.inr h₅)
      · exact Or.inr h₅
    · refine Or.inl (Or.inl ?_)
      by_contra h₅
      exact h₄ (hall.1 (by simpa only [Bool.not_eq_false] using h₅))

variable {u v w : GNode m}

theorem up_irrefl : Up S M f u u = false := Bool.eq_false_iff.2 fun h => (up_iff.1 h).1 rfl

theorem Tie.trans' {a b c : GNode m} (h₁ : Tie f a b) (h₂ : Tie f b c) : Tie f a c := by
  unfold Tie at *
  omega

theorem Tie.irrefl' {a : GNode m} : ¬ Tie f a a := by
  unfold Tie
  omega

theorem up_trans (h₁ : Up S M f u v = true) (h₂ : Up S M f v w = true) : Up S M f u w = true := by
  obtain ⟨hne, hs, ht⟩ := up_iff.1 h₁
  obtain ⟨hne', hs', ht'⟩ := up_iff.1 h₂
  refine up_iff.2 ⟨?_, hs'.trans' hs, fun h => ?_⟩
  · rintro rfl
    exact Tie.irrefl' ((ht hs').trans' (ht' hs))
  · exact (ht (h.trans' hs')).trans' (ht' (hs.trans' h))

/-- The standing hypotheses on the rows and the labels. -/
structure Std (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : Prop where
  lab : IsLab S M f
  ne : M ≠ []
  one : ∀ i, ∃ r ∈ M, r i ≠ S i

theorem Std.nonempty_cl (hs : Std S M f) (hv : Valid S M f v) : ∃ r ∈ M, v.cl S f r = true := by
  cases v with
  | root =>
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil M hs.ne
    exact ⟨r, hr, rfl⟩
  | top c =>
    obtain ⟨k, rfl⟩ := hv
    obtain ⟨r, hr, hri⟩ := hs.one k
    exact ⟨r, hr, decide_eq_true (mk_ne_iff.2 ⟨k, rfl, hri⟩)⟩
  | part c σ =>
    obtain ⟨⟨r, hr, h⟩, -⟩ := mem_rowsOf.1 hv.2
    exact ⟨r, hr, decide_eq_true h⟩
  | leaf ρ => exact ⟨ρ, hv, decide_eq_true rfl⟩

/-- A component with conflicts has two sequences off the ancestral one. -/
theorem Std.two_parts (hs : Std S M f) {c : Fin m} (hc : isNT f c = true) : ∃ r ∈ M, ∃ r' ∈ M, mkRow S f c r ≠ S ∧ mkRow S f c r' ≠ S ∧ mkRow S f c r ≠ mkRow S f c r' := by
  have hlen : 1 < (sitesOf f c).length := by simpa [isNT] using hc
  have hnd : (sitesOf f c).Nodup := (List.nodup_finRange m).filter _
  rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff] at hlen
  obtain ⟨a, b, ha, hb, hab⟩ := hlen
  have hfa : f a = c := by simpa [sitesOf] using ha
  have hfb : f b = c := by simpa [sitesOf] using hb
  obtain ⟨k, hk⟩ := exists_adj_of_reachable ((hs.lab a b).1 (hfa.trans hfb.symm)) hab
  have hkc : f k = c := ((hs.lab a k).2 (SimpleGraph.Adj.reachable hk)).symm.trans hfa
  have hne : (!S a) ≠ S a := by cases S a <;> simp
  have hrow : ∀ b' : Bool, ∃ r ∈ M, r a = !S a ∧ r k = b' := by
    intro b'
    obtain ⟨r, hr, h₁, h₂⟩ := hk (!S a) b'
    rcases mem_addRow.1 hr with rfl | hr'
    · exact absurd h₁.symm hne
    · exact ⟨r, List.mem_toFinset.1 hr', h₁, h₂⟩
  obtain ⟨r, hr, h₁, h₂⟩ := hrow true
  obtain ⟨r', hr', h₁', h₂'⟩ := hrow false
  refine ⟨r, hr, r', hr', mk_ne_iff.2 ⟨a, hfa, by rw [h₁]; exact hne⟩, mk_ne_iff.2 ⟨a, hfa, by rw [h₁']; exact hne⟩, fun h => ?_⟩
  have := congrFun h k
  simp [mkRow, hkc, h₂, h₂'] at this

/-- `trichotomy` for labels of components. -/
theorem Std.tri (hs : Std S M f) {c c' : Fin m} (hc : ∃ k, f k = c) (hc' : ∃ k, f k = c') (hne : c ≠ c') :
    (∀ r ∈ M, mkRow S f c r = S ∨ mkRow S f c' r = S) ∨ (∃ σ, σ ≠ S ∧ ∀ r ∈ M, mkRow S f c' r ≠ S → mkRow S f c r = σ) ∨ (∃ σ', σ' ≠ S ∧ ∀ r ∈ M, mkRow S f c r ≠ S → mkRow S f c' r = σ') := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨k', rfl⟩ := hc'
  exact trichotomy hs.lab hne

theorem cl_top {c : Fin m} {r : Row m} : (GNode.top c).cl S f r = true ↔ mkRow S f c r ≠ S := by simp [GNode.cl]

theorem cl_part {c : Fin m} {σ r : Row m} : (GNode.part c σ).cl S f r = true ↔ mkRow S f c r = σ := by simp [GNode.cl]

theorem cl_leaf {ρ r : Row m} : (GNode.leaf ρ).cl S f r = true ↔ r = ρ := by simp [GNode.cl]

theorem exists_of_isNT {c : Fin m} (hc : isNT f c = true) : ∃ k, f k = c := by
  have hlen : 1 < (sitesOf f c).length := by simpa [isNT] using hc
  have hne : sitesOf f c ≠ [] := fun h => by
    rw [h] at hlen
    simp at hlen
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨a, by simpa [sitesOf] using ha⟩

/-- **Nested or disjoint**: the clusters of two nodes. -/
theorem Std.laminar (hs : Std S M f) (hu : Valid S M f u) (hv : Valid S M f v) (r : Row m) (hr : r ∈ M) (h₁ : u.cl S f r = true) (h₂ : v.cl S f r = true) : SubCl S M f u v ∨ SubCl S M f v u := by
  have hroot : ∀ {x : GNode m}, SubCl S M f x .root := fun _ _ _ => rfl
  have hleaf : ∀ {x : GNode m} {ρ : Row m}, x.cl S f ρ = true → SubCl S M f (.leaf ρ) x := by
    intro x ρ hx r' _ h'
    rw [cl_leaf.1 h']
    exact hx
  have hsame : ∀ {c : Fin m} {σ : Row m}, (mkRow S f c r = σ) → σ ≠ S → SubCl S M f (.part c σ) (.top c) := by
    intro c σ _ hσ r' _ h'
    rw [cl_top, cl_part.1 h']
    exact hσ
  cases u with
  | root => exact Or.inr hroot
  | leaf ρ => exact Or.inl (hleaf (by rwa [← cl_leaf.1 h₁]))
  | top c =>
    cases v with
    | root => exact Or.inl hroot
    | leaf ρ => exact Or.inr (hleaf (by rwa [← cl_leaf.1 h₂]))
    | top c' =>
      by_cases hcc : c = c'
      · subst hcc
        exact Or.inl fun _ _ h => h
      rcases hs.tri hu hv hcc with h | ⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd h' (cl_top.1 h₁)
        · exact absurd h' (cl_top.1 h₂)
      · exact Or.inr fun r' hr' h' => cl_top.2 (by rw [h r' hr' (cl_top.1 h')]; exact hσ)
      · exact Or.inl fun r' hr' h' => cl_top.2 (by rw [h r' hr' (cl_top.1 h')]; exact hσ)
    | part c' τ =>
      by_cases hcc : c = c'
      · subst hcc
        exact Or.inr (hsame (cl_part.1 h₂) (mem_rowsOf.1 hv.2).2)
      rcases hs.tri hu (exists_of_isNT hv.1) hcc with h | ⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd h' (cl_top.1 h₁)
        · exact absurd (h'.symm.trans (cl_part.1 h₂)) (mem_rowsOf.1 hv.2).2.symm
      · refine Or.inr fun r' hr' h' => cl_top.2 ?_
        have hne : mkRow S f c' r' ≠ S := by
          rw [cl_part.1 h']
          exact (mem_rowsOf.1 hv.2).2
        rw [h r' hr' hne]
        exact hσ
      · refine Or.inl fun r' hr' h' => cl_part.2 ?_
        rw [h r' hr' (cl_top.1 h'), ← h r hr (cl_top.1 h₁)]
        exact cl_part.1 h₂
  | part c σ =>
    have hmemσ := mem_rowsOf.1 hu.2
    cases v with
    | root => exact Or.inl hroot
    | leaf ρ => exact Or.inr (hleaf (by rwa [← cl_leaf.1 h₂]))
    | top c' =>
      by_cases hcc : c = c'
      · subst hcc
        exact Or.inl (hsame (cl_part.1 h₁) hmemσ.2)
      rcases hs.tri (exists_of_isNT hu.1) hv hcc with h | ⟨τ, hτ, h⟩ | ⟨τ, hτ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd (h'.symm.trans (cl_part.1 h₁)) hmemσ.2.symm
        · exact absurd h' (cl_top.1 h₂)
      · refine Or.inr fun r' hr' h' => cl_part.2 ?_
        rw [h r' hr' (cl_top.1 h'), ← h r hr (cl_top.1 h₂)]
        exact cl_part.1 h₁
      · refine Or.inl fun r' hr' h' => cl_top.2 ?_
        have hne : mkRow S f c r' ≠ S := by
          rw [cl_part.1 h']
          exact hmemσ.2
        rw [h r' hr' hne]
        exact hτ
    | part c' τ =>
      have hmemτ := mem_rowsOf.1 hv.2
      by_cases hcc : c = c'
      · subst hcc
        obtain rfl : σ = τ := (cl_part.1 h₁).symm.trans (cl_part.1 h₂)
        exact Or.inl fun _ _ h => h
      rcases hs.tri (exists_of_isNT hu.1) (exists_of_isNT hv.1) hcc with h | ⟨ρ, hρ, h⟩ | ⟨ρ, hρ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd (h'.symm.trans (cl_part.1 h₁)) hmemσ.2.symm
        · exact absurd (h'.symm.trans (cl_part.1 h₂)) hmemτ.2.symm
      · refine Or.inr fun r' hr' h' => cl_part.2 ?_
        have hne : ∀ {r₀}, (GNode.part c' τ).cl S f r₀ = true → mkRow S f c' r₀ ≠ S := fun {r₀} h₀ => by
          rw [cl_part.1 h₀]
          exact hmemτ.2
        rw [h r' hr' (hne h'), ← h r hr (hne h₂)]
        exact cl_part.1 h₁
      · refine Or.inl fun r' hr' h' => cl_part.2 ?_
        have hne : ∀ {r₀}, (GNode.part c σ).cl S f r₀ = true → mkRow S f c r₀ ≠ S := fun {r₀} h₀ => by
          rw [cl_part.1 h₀]
          exact hmemσ.2
        rw [h r' hr' (hne h'), ← h r hr (hne h₁)]
        exact cl_part.1 h₂

/-! ### The order on the nodes -/

theorem Tie.total {u v : GNode m} (hu : Valid S M f u) (hv : Valid S M f v) (hne : u ≠ v) (hr : ∃ r, u.cl S f r = true ∧ v.cl S f r = true) : Tie f u v ∨ Tie f v u := by
  have hval : ∀ {x y : ℕ}, x ≠ y → x < y ∨ y < x := fun h => Nat.lt_or_gt_of_ne h
  obtain ⟨r, h₁, h₂⟩ := hr
  have hsame : u.rank f = v.rank f → u.idx ≠ v.idx := by
    intro hrk hidx
    apply hne
    cases u <;> cases v <;> simp only [GNode.rank, GNode.idx] at hrk hidx
    · rfl
    · split_ifs at hrk
    · simp at hrk
    · simp at hrk
    · split_ifs at hrk
    · rw [Fin.ext hidx]
    · split_ifs at hrk <;> omega
    · split_ifs at hrk <;> omega
    · simp at hrk
    · split_ifs at hrk <;> omega
    · have hcc := Fin.ext hidx
      subst hcc
      rw [(cl_part.1 h₁).symm.trans (cl_part.1 h₂)]
    · simp at hrk
    · simp at hrk
    · split_ifs at hrk <;> omega
    · simp at hrk
    · rw [(cl_leaf.1 h₁).symm.trans (cl_leaf.1 h₂)]
  by_cases hrk : u.rank f = v.rank f
  · rcases hval (hsame hrk) with h | h
    · exact Or.inl (Or.inr ⟨hrk, h⟩)
    · exact Or.inr (Or.inr ⟨hrk.symm, h⟩)
  · rcases hval hrk with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

/-- Two nodes above a third are in a line. -/
theorem Std.chain (hs : Std S M f) {u u' v : GNode m} (hu : Valid S M f u) (hu' : Valid S M f u') (hv : Valid S M f v) (h : Up S M f u v = true) (h' : Up S M f u' v = true) :
    u = u' ∨ Up S M f u u' = true ∨ Up S M f u' u = true := by
  by_cases hne : u = u'
  · exact Or.inl hne
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  have h₁ := (up_iff.1 h).2.1 r hr hrv
  have h₂ := (up_iff.1 h').2.1 r hr hrv
  right
  rcases hs.laminar hu hu' r hr h₁ h₂ with hsub | hsub
  · by_cases hsub' : SubCl S M f u' u
    · rcases Tie.total hu hu' hne ⟨r, h₁, h₂⟩ with ht | ht
      · exact Or.inl (up_iff.2 ⟨hne, hsub', fun _ => ht⟩)
      · exact Or.inr (up_iff.2 ⟨Ne.symm hne, hsub, fun _ => ht⟩)
    · exact Or.inr (up_iff.2 ⟨Ne.symm hne, hsub, fun h₃ => absurd h₃ hsub'⟩)
  · by_cases hsub' : SubCl S M f u u'
    · rcases Tie.total hu hu' hne ⟨r, h₁, h₂⟩ with ht | ht
      · exact Or.inl (up_iff.2 ⟨hne, hsub, fun _ => ht⟩)
      · exact Or.inr (up_iff.2 ⟨Ne.symm hne, hsub', fun _ => ht⟩)
    · exact Or.inl (up_iff.2 ⟨hne, hsub, fun h₃ => absurd h₃ hsub'⟩)

/-- A leaf is above nothing. -/
theorem Std.not_up_leaf (hs : Std S M f) (hv : Valid S M f v) {ρ : Row m} : Up S M f (.leaf ρ) v = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨hne, h₁, h₂⟩ := up_iff.1 h
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  have hrρ : r = ρ := cl_leaf.1 (h₁ r hr hrv)
  subst hrρ
  have h₃ : SubCl S M f (.leaf r) v := fun r' _ h' => by
    rw [cl_leaf.1 h']
    exact hrv
  have hrk : ∀ w : GNode m, w.rank f ≤ 4 := by
    intro w
    cases w <;> simp only [GNode.rank]
    · omega
    · split_ifs <;> omega
    · omega
    · omega
  have h₄ := h₂ h₃
  have := hrk v
  have hidx0 : v.rank f = 4 → v.idx = 0 := by
    intro h₅
    cases v with
    | root => rfl
    | leaf _ => rfl
    | part _ _ => simp [GNode.rank] at h₅
    | top c =>
      simp only [GNode.rank] at h₅
      split_ifs at h₅ <;> omega
  have hL : (GNode.leaf r : GNode m).rank f = 4 := rfl
  have hLi : (GNode.leaf r : GNode m).idx = 0 := rfl
  unfold Tie at h₄
  rw [hL, hLi] at h₄
  rcases h₄ with h₅ | ⟨h₅, h₆⟩
  · omega
  · have := hidx0 h₅.symm
    omega

theorem length_filter_le' {β : Type*} {l : List β} {p q : β → Bool} (hpq : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    have ha := hpq a List.mem_cons_self
    simp only [List.filter_cons]
    by_cases hp : p a = true
    · simp [hp, ha hp]
      omega
    · by_cases hq : q a = true
      · simp [hp, hq]
        omega
      · simp [hp, hq]
        omega

theorem length_filter_lt {β : Type*} {l : List β} {p q : β → Bool} (hpq : ∀ x ∈ l, p x = true → q x = true) (h : ∃ x ∈ l, q x = true ∧ p x = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    have hle := length_filter_le' (l := t) fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    have ha := hpq a List.mem_cons_self
    obtain ⟨x, hx, hqx, hpx⟩ := h
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [hqx, hpx]
      omega
    · have hlt := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hqx, hpx⟩
      by_cases hp : p a = true
      · simp [hp, ha hp]
        omega
      · by_cases hq : q a = true
        · simp [hp, hq]
          omega
        · simp [hp, hq]
          omega

theorem rank_le (w : GNode m) : w.rank f ≤ 4 := by
  cases w <;> simp only [GNode.rank]
  · omega
  · split_ifs <;> omega
  · omega
  · omega

theorem idx_le (w : GNode m) : w.idx ≤ m := by
  cases w <;> simp only [GNode.idx]
  · omega
  · exact Nat.le_of_lt (Fin.is_lt _)
  · exact Nat.le_of_lt (Fin.is_lt _)
  · omega

/-- The key goes up along `Up`. -/
theorem key_lt {u v : GNode m} (h : Up S M f u v = true) : key S M f u < key S M f v := by
  obtain ⟨-, h₁, h₂⟩ := up_iff.1 h
  have hu := idx_le u
  have hv := idx_le v
  have hru := rank_le (f := f) u
  have hrv := rank_le (f := f) v
  have hbound : u.rank f * (m + 1) + u.idx ≤ 4 * (m + 1) + m := by nlinarith
  have hle : (M.filter (v.cl S f)).length ≤ (M.filter (u.cl S f)).length := length_filter_le' fun x hx => h₁ x hx
  have hleM : (M.filter (u.cl S f)).length ≤ M.length := List.length_filter_le _ _
  unfold key
  by_cases hsub : SubCl S M f u v
  · have heq : (M.filter (u.cl S f)).length = (M.filter (v.cl S f)).length := le_antisymm (length_filter_le' fun x hx => hsub x hx) hle
    rw [heq]
    rcases h₂ hsub with ht | ⟨ht, hi⟩
    · have : (u.rank f + 1) * (m + 1) ≤ v.rank f * (m + 1) := Nat.mul_le_mul_right _ ht
      nlinarith
    · rw [ht]
      omega
  · unfold SubCl at hsub
    push Not at hsub
    obtain ⟨r, hr, h₃, h₄⟩ := hsub
    have hlt : (M.filter (v.cl S f)).length < (M.filter (u.cl S f)).length := length_filter_lt (fun x hx => h₁ x hx) ⟨r, hr, h₃, by simpa using h₄⟩
    obtain ⟨d, hd⟩ : ∃ d, M.length - (M.filter (v.cl S f)).length = M.length - (M.filter (u.cl S f)).length + 1 + d := ⟨M.length - (M.filter (v.cl S f)).length - (M.length - (M.filter (u.cl S f)).length) - 1, by omega⟩
    rw [hd]
    nlinarith [Nat.zero_le (d * (6 * (m + 1))), Nat.zero_le (v.rank f * (m + 1))]

theorem mem_reps {c : Fin m} : c ∈ reps f ↔ ∃ k, f k = c := by
  simp [reps]

theorem valid_of_mem_cands {u : GNode m} (h : u ∈ cands S M f) : Valid S M f u := by
  rcases List.mem_cons.1 h with rfl | h
  · trivial
  rcases List.mem_append.1 h with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    exact mem_reps.1 hc
  · obtain ⟨c, hc, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 h'
    exact ⟨(List.mem_filter.1 hc).2, hσ⟩

theorem mem_cands_of_valid {u : GNode m} (h : Valid S M f u) (hl : ∀ ρ, u ≠ .leaf ρ) : u ∈ cands S M f := by
  cases u with
  | root => exact List.mem_cons_self
  | top c => exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨c, mem_reps.2 h, rfl⟩))
  | part c σ => exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨c, List.mem_filter.2 ⟨mem_reps.2 (exists_of_isNT h.1), h.1⟩, List.mem_map.2 ⟨σ, h.2, rfl⟩⟩))
  | leaf ρ => exact absurd rfl (hl ρ)

/-- The root is above all the other nodes. -/
theorem up_root {v : GNode m} (hne : v ≠ .root) : Up S M f .root v = true := by
  refine up_iff.2 ⟨hne.symm, fun _ _ _ => rfl, fun _ => Or.inl ?_⟩
  cases v with
  | root => exact absurd rfl hne
  | top c =>
    simp only [GNode.rank]
    split_ifs <;> omega
  | part _ _ => simp [GNode.rank]
  | leaf _ => simp [GNode.rank]

/-- **The parent by clusters**: the lowest of the nodes above a node. -/
theorem Std.treePar_spec (hs : Std S M f) {v : GNode m} (hv : Valid S M f v) (hne : v ≠ .root) :
    ∃ u, treePar S M f v = some u ∧ Valid S M f u ∧ (∀ ρ, u ≠ .leaf ρ) ∧ Up S M f u v = true ∧ ∀ u', Valid S M f u' → Up S M f u' v = true → u' = u ∨ Up S M f u' u = true := by
  have hrootm : (GNode.root : GNode m) ∈ (cands S M f).filter fun u => Up S M f u v := List.mem_filter.2 ⟨mem_cands_of_valid trivial (by simp), up_root hne⟩
  have hnone : ((cands S M f).filter fun u => Up S M f u v).argmax (key S M f) ≠ none := by
    rw [Ne, List.argmax_eq_none]
    intro h
    rw [h] at hrootm
    simp at hrootm
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hnone
  have humem := List.argmax_mem hu
  obtain ⟨huc, huv⟩ := List.mem_filter.1 humem
  have hul : ∀ ρ, u ≠ .leaf ρ := by
    rintro ρ rfl
    rw [hs.not_up_leaf hv] at huv
    exact absurd huv (by simp)
  refine ⟨u, hu, valid_of_mem_cands huc, hul, huv, fun u' hu' h' => ?_⟩
  have hu'l : ∀ ρ, u' ≠ .leaf ρ := by
    rintro ρ rfl
    rw [hs.not_up_leaf hv] at h'
    exact absurd h' (by simp)
  rcases hs.chain hu' (valid_of_mem_cands huc) hv h' huv with h₁ | h₁ | h₁
  · exact Or.inl h₁
  · exact Or.inr h₁
  · have hle := List.le_of_mem_argmax (List.mem_filter.2 ⟨mem_cands_of_valid hu' hu'l, h'⟩) hu
    have hlt := key_lt h₁
    omega

/-! ### The nodes of a gall among the others -/

theorem Std.top_up_part (hs : Std S M f) {c : Fin m} {σ : Row m} (hc : isNT f c = true) (hσ : σ ∈ rowsOf S M f c) : Up S M f (.top c) (.part c σ) = true := by
  refine up_iff.2 ⟨by simp, fun r _ h => cl_top.2 ?_, fun h => ?_⟩
  · rw [cl_part.1 h]
    exact (mem_rowsOf.1 hσ).2
  · exfalso
    obtain ⟨r, hr, r', hr', h₁, h₂, h₃⟩ := hs.two_parts hc
    exact h₃ ((cl_part.1 (h r hr (cl_top.2 h₁))).trans (cl_part.1 (h r' hr' (cl_top.2 h₂))).symm)

theorem not_up_part_part {c : Fin m} {σ τ : Row m} (hσ : σ ∈ rowsOf S M f c) : Up S M f (.part c τ) (.part c σ) = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨h₁, h₂, -⟩ := up_iff.1 h
  obtain ⟨⟨r, hr, hrσ⟩, -⟩ := mem_rowsOf.1 hσ
  have := cl_part.1 (h₂ r hr (cl_part.2 hrσ))
  apply h₁
  rw [← this, hrσ]

theorem Std.not_up_part_top (hs : Std S M f) {c : Fin m} {τ : Row m} (hc : isNT f c = true) : Up S M f (.part c τ) (.top c) = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨-, h₂, -⟩ := up_iff.1 h
  obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hc
  exact h₅ ((cl_part.1 (h₂ r hr (cl_top.2 h₃))).trans (cl_part.1 (h₂ r' hr' (cl_top.2 h₄))).symm)

theorem rank_top_ge {c : Fin m} : 2 ≤ (GNode.top c : GNode m).rank f := by
  simp only [GNode.rank]
  split_ifs <;> omega

theorem not_tie_top {c : Fin m} {v : GNode m} (hv : v.rank f < 2) : ¬ Tie f (.top c) v := by
  have := rank_top_ge (f := f) (c := c)
  unfold Tie
  omega

/-- What is above a node of a gall, off the gall, is above the coalescent node. -/
theorem Std.up_top_of_up_part (hs : Std S M f) {c : Fin m} {σ : Row m} (hc : isNT f c = true) (hσ : σ ∈ rowsOf S M f c) {k : GNode m} (hk : Valid S M f k) (hk₁ : k ≠ .top c) (hk₂ : ∀ τ, k ≠ .part c τ)
    (h : Up S M f k (.part c σ) = true) : Up S M f k (.top c) = true := by
  obtain ⟨-, hsub, htie⟩ := up_iff.1 h
  have hσv : Valid S M f (.part c σ) := ⟨hc, hσ⟩
  obtain ⟨⟨r₀, hr₀, hr₀σ⟩, hσS⟩ := mem_rowsOf.1 hσ
  have hr₀k := hsub r₀ hr₀ (cl_part.2 hr₀σ)
  have hrc : mkRow S f c r₀ ≠ S := by rw [hr₀σ]; exact hσS
  refine up_iff.2 ⟨hk₁, ?_, ?_⟩
  · cases k with
    | root => exact fun _ _ _ => rfl
    | leaf ρ => exact absurd h (by rw [hs.not_up_leaf hσv]; simp)
    | top c' =>
      have hcc : c ≠ c' := fun h' => hk₁ (by rw [h'])
      rcases hs.tri (exists_of_isNT hc) hk hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', hσ', h'⟩
      · exfalso
        rcases h' r₀ hr₀ with h₁ | h₁
        · exact hrc h₁
        · exact cl_top.1 hr₀k h₁
      · exfalso
        have hσ₁ : σ = σ₁ := hr₀σ.symm.trans (h' r₀ hr₀ (cl_top.1 hr₀k))
        exact not_tie_top (by simp [GNode.rank]) (htie fun r hr hrk => cl_part.2 ((h' r hr (cl_top.1 hrk)).trans hσ₁.symm))
      · exact fun r hr hrt => cl_top.2 (by rw [h' r hr (cl_top.1 hrt)]; exact hσ')
    | part c' τ =>
      have hcc : c ≠ c' := by
        rintro rfl
        exact hk₂ τ rfl
      have hτS := (mem_rowsOf.1 hk.2).2
      rcases hs.tri (exists_of_isNT hc) (exists_of_isNT hk.1) hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
      · exfalso
        rcases h' r₀ hr₀ with h₁ | h₁
        · exact hrc h₁
        · exact hτS ((cl_part.1 hr₀k).symm.trans h₁)
      · exfalso
        obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hk.1
        have hσ₁ : σ = σ₁ := hr₀σ.symm.trans (h' r₀ hr₀ (by rw [cl_part.1 hr₀k]; exact hτS))
        have hin : ∀ {x}, x ∈ M → mkRow S f c' x ≠ S → mkRow S f c' x = τ := fun {x} hx hxn =>
          cl_part.1 (hsub x hx (cl_part.2 ((h' x hx hxn).trans hσ₁.symm)))
        exact h₅ ((hin hr h₃).trans (hin hr' h₄).symm)
      · have hτ : τ = σ' := (cl_part.1 hr₀k).symm.trans (h' r₀ hr₀ hrc)
        exact fun r hr hrt => cl_part.2 ((h' r hr (cl_top.1 hrt)).trans hτ.symm)
  · intro hsub'
    cases k with
    | root => exact Or.inl (by simp only [GNode.rank, hc, ite_true]; omega)
    | leaf ρ => exact absurd h (by rw [hs.not_up_leaf hσv]; simp)
    | part c' τ => exact Or.inl (by simp only [GNode.rank, hc, ite_true]; omega)
    | top c' =>
      have hcc : c ≠ c' := fun h' => hk₁ (by rw [h'])
      refine Or.inl ?_
      simp only [GNode.rank, hc, ite_true]
      by_cases hc' : isNT f c' = true
      · exfalso
        obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hc'
        rcases hs.tri (exists_of_isNT hc) hk hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
        · rcases h' r₀ hr₀ with h₁ | h₁
          · exact hrc h₁
          · exact cl_top.1 hr₀k h₁
        · have hσ₁ : σ = σ₁ := hr₀σ.symm.trans (h' r₀ hr₀ (cl_top.1 hr₀k))
          have hin : ∀ {x}, x ∈ M → mkRow S f c' x ≠ S → mkRow S f c x = σ₁ := fun {x} hx hxn => h' x hx hxn
          exact not_tie_top (by simp [GNode.rank]) (htie fun x hx hxk => cl_part.2 ((hin hx (cl_top.1 hxk)).trans hσ₁.symm))
        · exact h₅ ((h' r hr (cl_top.1 (hsub' r hr (cl_top.2 h₃)))).trans (h' r' hr' (cl_top.1 (hsub' r' hr' (cl_top.2 h₄)))).symm)
      · simp [hc']

/-- A coalescent node above a node off its gall has a node of the gall above that node too: the rows of the node are at one sequence of the component. -/
theorem Std.exists_part_of_up_top (hs : Std S M f) {c : Fin m} (hc : isNT f c = true) {v : GNode m} (hv : Valid S M f v) (hv₁ : v ≠ .top c) (hv₂ : ∀ τ, v ≠ .part c τ)
    (h : Up S M f (.top c) v = true) : ∃ τ ∈ rowsOf S M f c, Up S M f (.part c τ) v = true := by
  obtain ⟨-, hsub, htie⟩ := up_iff.1 h
  obtain ⟨r₀, hr₀, hr₀v⟩ := hs.nonempty_cl hv
  have hr₀c : mkRow S f c r₀ ≠ S := cl_top.1 (hsub r₀ hr₀ hr₀v)
  have hτ : mkRow S f c r₀ ∈ rowsOf S M f c := mem_rowsOf.2 ⟨⟨r₀, hr₀, rfl⟩, hr₀c⟩
  refine ⟨_, hτ, ?_⟩
  cases v with
  | root =>
    exact absurd (htie fun _ _ _ => rfl) (not_tie_top (by simp [GNode.rank]))
  | leaf ρ =>
    obtain rfl := cl_leaf.1 hr₀v
    refine up_iff.2 ⟨by simp, fun r _ h' => ?_, fun _ => Or.inl (by simp [GNode.rank])⟩
    rw [cl_leaf.1 h']
    exact cl_part.2 rfl
  | top c₂ =>
    have hcc : c₂ ≠ c := fun h' => hv₁ (by rw [h'])
    rcases hs.tri hv (exists_of_isNT hc) hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
    · exfalso
      rcases h' r₀ hr₀ with h₁ | h₁
      · exact cl_top.1 hr₀v h₁
      · exact hr₀c h₁
    · exfalso
      have hsub₂ : SubCl S M f (.top c) (.top c₂) := fun r hr hrt => cl_top.2 (by
        rw [h' r hr (cl_top.1 hrt), ← h' r₀ hr₀ hr₀c]
        exact cl_top.1 hr₀v)
      by_cases hc₂ : isNT f c₂ = true
      · obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hc₂
        exact h₅ ((h' r hr (cl_top.1 (hsub r hr (cl_top.2 h₃)))).trans (h' r' hr' (cl_top.1 (hsub r' hr' (cl_top.2 h₄)))).symm)
      · have ht := htie hsub₂
        have hr₁ : (GNode.top c : GNode m).rank f = 3 := by simp [GNode.rank, hc]
        have hr₂ : (GNode.top c₂ : GNode m).rank f = 2 := by simp [GNode.rank, hc₂]
        unfold Tie at ht
        rw [hr₁, hr₂] at ht
        omega
    · have hτ' : mkRow S f c r₀ = σ' := h' r₀ hr₀ (cl_top.1 hr₀v)
      refine up_iff.2 ⟨by simp, fun r hr hrt => cl_part.2 ((h' r hr (cl_top.1 hrt)).trans hτ'.symm), fun _ => Or.inl ?_⟩
      have := rank_top_ge (f := f) (c := c₂)
      simp only [GNode.rank] at this ⊢
      omega
  | part c₂ σ₂ =>
    have hcc : c₂ ≠ c := by
      rintro rfl
      exact hv₂ σ₂ rfl
    have hσ₂S := (mem_rowsOf.1 hv.2).2
    have hne₂ : ∀ {x}, (GNode.part c₂ σ₂).cl S f x = true → mkRow S f c₂ x ≠ S := fun {x} hx => by
      rw [cl_part.1 hx]
      exact hσ₂S
    rcases hs.tri (exists_of_isNT hv.1) (exists_of_isNT hc) hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
    · exfalso
      rcases h' r₀ hr₀ with h₁ | h₁
      · exact hne₂ hr₀v h₁
      · exact hr₀c h₁
    · exfalso
      have hσ₁ : σ₂ = σ₁ := (cl_part.1 hr₀v).symm.trans (h' r₀ hr₀ hr₀c)
      exact not_tie_top (by simp [GNode.rank]) (htie fun r hr hrt => cl_part.2 ((h' r hr (cl_top.1 hrt)).trans hσ₁.symm))
    · have hτ' : mkRow S f c r₀ = σ' := h' r₀ hr₀ (hne₂ hr₀v)
      refine up_iff.2 ⟨by
        intro h₀
        exact hcc ((GNode.part.inj h₀).1.symm), fun r hr hrt => cl_part.2 ((h' r hr (hne₂ hrt)).trans hτ'.symm), fun hsub₂ => ?_⟩
      exfalso
      obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hv.1
      have hin : ∀ {x}, x ∈ M → mkRow S f c₂ x ≠ S → mkRow S f c₂ x = σ₂ := fun {x} hx hxn => cl_part.1 (hsub₂ x hx (cl_part.2 ((h' x hx hxn).trans hτ'.symm)))
      exact h₅ ((hin hr h₃).trans (hin hr' h₄).symm)

/-! ### Chains -/

/-- The `1`s of `x` are `1`s of `y`. -/
def Sub1 (S x y : Row m) : Prop := ∀ i, x i ≠ S i → y i ≠ S i

theorem Sub1.refl' (x : Row m) : Sub1 S x x := fun _ h => h

theorem Sub1.trans' {x y z : Row m} (h₁ : Sub1 S x y) (h₂ : Sub1 S y z) : Sub1 S x z := fun i hi => h₂ i (h₁ i hi)

theorem card1_le {x y : Row m} (h : Sub1 S x y) : card1 S x ≤ card1 S y :=
  length_filter_le' fun i _ hi => by simpa using h i (by simpa using hi)

theorem eq_of_sub1 {x y : Row m} (h : Sub1 S x y) (h' : Sub1 S y x) : x = y := by
  funext i
  have h₁ := h i
  have h₂ := h' i
  revert h₁ h₂
  cases x i <;> cases y i <;> cases S i <;> simp

theorem card1_lt {x y : Row m} (h : Sub1 S x y) (hne : x ≠ y) : card1 S x < card1 S y := by
  have hi : ∃ i, y i ≠ S i ∧ x i = S i := by
    by_contra hno
    push Not at hno
    exact hne (eq_of_sub1 h fun i hi => hno i hi)
  obtain ⟨i, h₁, h₂⟩ := hi
  exact length_filter_lt (fun j _ hj => by simpa using h j (by simpa using hj)) ⟨i, List.mem_finRange i, by simpa using h₁, by simpa using h₂⟩

/-- A chain of rows. -/
def Ch (S : Row m) (X : List (Row m)) : Prop := ∀ x ∈ X, ∀ y ∈ X, Sub1 S x y ∨ Sub1 S y x

theorem Ch.sub_of_le {X : List (Row m)} (h : Ch S X) {x y : Row m} (hx : x ∈ X) (hy : y ∈ X) (hle : card1 S x ≤ card1 S y) : Sub1 S x y := by
  rcases h x hx y hy with h' | h'
  · exact h'
  · by_cases hne : y = x
    · rw [hne]
      exact Sub1.refl' x
    · have := card1_lt h' hne
      omega

theorem Ch.filter {X : List (Row m)} (h : Ch S X) (p : Row m → Bool) : Ch S (X.filter p) := fun x hx y hy =>
  h x (List.mem_filter.1 hx).1 y (List.mem_filter.1 hy).1

/-- The end of a chain. -/
theorem endNode_spec {X : List (Row m)} (hX : Ch S X) (c : Fin m) : (X = [] ∧ endNode S c X = .top c) ∨ ∃ y ∈ X, endNode S c X = .part c y ∧ ∀ a ∈ X, Sub1 S a y := by
  cases hm : X.argmax (card1 S) with
  | none =>
    refine Or.inl ⟨List.argmax_eq_none.1 hm, ?_⟩
    simp [endNode, hm]
  | some y =>
    have hy := List.argmax_mem hm
    refine Or.inr ⟨y, hy, by simp [endNode, hm], fun a ha => hX.sub_of_le ha hy (List.le_of_mem_argmax ha hm)⟩

theorem topAt_eq_of_max {X : List (Row m)} {y : Row m} (hy : y ∈ X) (hmax : ∀ a ∈ X, Sub1 S a y) (i : Fin m) : topAt S X i = y i := by
  have hb : ∀ {a b c : Bool}, (a ≠ c ↔ b ≠ c) → a = b := by decide
  refine hb (c := S i) (topAt_ne_iff.trans ⟨?_, fun h => ⟨y, hy, h⟩⟩)
  rintro ⟨r, hr, hri⟩
  exact hmax r hr i hri

theorem topAt_nil (i : Fin m) : topAt S [] i = S i := by simp [topAt]

/-- The node before a row of a chain. -/
theorem predNode_spec {X : List (Row m)} (hX : Ch S X) (c : Fin m) {σ : Row m} (hσ : σ ∈ X) :
    (predNode S c X σ = .top c ∧ ∀ a ∈ X, Sub1 S a σ → a = σ) ∨ ∃ y ∈ X, predNode S c X σ = .part c y ∧ Sub1 S y σ ∧ y ≠ σ ∧ card1 S y < card1 S σ ∧ ∀ a ∈ X, Sub1 S a σ → a ≠ σ → Sub1 S a y := by
  rcases endNode_spec (hX.filter fun y => decide (card1 S y < card1 S σ)) c with ⟨h₁, h₂⟩ | ⟨y, hy, h₂, h₃⟩
  · refine Or.inl ⟨h₂, fun a ha hsub => ?_⟩
    by_contra hne
    have : a ∈ X.filter fun y => decide (card1 S y < card1 S σ) := List.mem_filter.2 ⟨ha, by simpa using card1_lt hsub hne⟩
    rw [h₁] at this
    simp at this
  · obtain ⟨hyX, hyl⟩ := List.mem_filter.1 hy
    have hlt : card1 S y < card1 S σ := by simpa using hyl
    refine Or.inr ⟨y, hyX, h₂, hX.sub_of_le hyX hσ hlt.le, ?_, hlt, fun a ha hsub hne => h₃ a (List.mem_filter.2 ⟨ha, by simpa using card1_lt hsub hne⟩)⟩
    rintro rfl
    omega

/-- What the arrangement of a component gives. -/
structure ArrOK (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (c : Fin m) (a : Arr m) : Prop where
  s_mem : a.1 ∈ rowsOf S M f c
  X_mem : ∀ y ∈ a.2.1, y ∈ rowsOf S M f c ∧ y ≠ a.1
  Y_mem : ∀ y ∈ a.2.2, y ∈ rowsOf S M f c ∧ y ≠ a.1
  all : ∀ σ ∈ rowsOf S M f c, σ = a.1 ∨ σ ∈ a.2.1 ∨ σ ∈ a.2.2
  chX : Ch S a.2.1
  chY : Ch S a.2.2
  disj : ∀ x ∈ a.2.1, ∀ y ∈ a.2.2, ∀ i, x i ≠ S i → y i = S i
  cover : ∀ i, f i = c → (∃ y ∈ a.2.1, y i ≠ S i) ∨ ∃ y ∈ a.2.2, y i ≠ S i
  point : ∃ n, ∀ i, f i = c → a.1 i = if i.val < n then topAt S a.2.2 i else topAt S a.2.1 i

/-! ### The labels -/

section Labels

variable (hs : Std S M f)

include hs

theorem Std.part_unique {c : Fin m} {τ τ' : Row m} {v : GNode m} (hv : Valid S M f v) (h : Up S M f (.part c τ) v = true) (h' : Up S M f (.part c τ') v = true) : τ = τ' := by
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  exact (cl_part.1 ((up_iff.1 h).2.1 r hr hrv)).symm.trans (cl_part.1 ((up_iff.1 h').2.1 r hr hrv))

omit hs in
theorem label_part_self {i : Fin m} (hc : isNT f (f i) = true) (σ : Row m) : label S M f (.part (f i) σ) i = σ i := by
  simp [label, hc]

/-- The label at a site of a component, from the gall node above. -/
theorem Std.label_of_up {i : Fin m} (hc : isNT f (f i) = true) {τ : Row m} (hτ : τ ∈ rowsOf S M f (f i)) {v : GNode m} (hv : Valid S M f v) (hvo : ∀ σ, v ≠ .part (f i) σ) (h : Up S M f (.part (f i) τ) v = true) : label S M f v i = τ i := by
  have hfind : (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) = some τ := by
    cases hf : (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) with
    | none =>
      have := List.find?_eq_none.1 hf τ hτ
      rw [h] at this
      exact absurd this (by simp)
    | some τ' =>
      have h' := List.find?_some hf
      rw [hs.part_unique hv h' h]
  cases v with
  | part c' σ =>
    have hne : c' ≠ f i := by
      rintro rfl
      exact hvo σ rfl
    simp [label, hc, hne, hfind]
  | root => simp [label, hc, hfind]
  | top c' => simp [label, hc, hfind]
  | leaf ρ => simp [label, hc, hfind]

omit hs in
/-- The label at a site of a component, with no gall node above. -/
theorem label_of_not {i : Fin m} (hc : isNT f (f i) = true) {v : GNode m} (hvo : ∀ σ, v ≠ .part (f i) σ) (h : ∀ τ ∈ rowsOf S M f (f i), Up S M f (.part (f i) τ) v = false) : label S M f v i = S i := by
  have hfind : (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) = none := List.find?_eq_none.2 fun τ hτ => by simp [h τ hτ]
  cases v with
  | part c' σ =>
    have hne : c' ≠ f i := by
      rintro rfl
      exact hvo σ rfl
    simp [label, hc, hne, hfind]
  | root => simp [label, hc, hfind]
  | top c' => simp [label, hc, hfind]
  | leaf ρ => simp [label, hc, hfind]

omit hs in
/-- The label at a site alone in its component. -/
theorem label_trivial {i : Fin m} (hc : ¬ isNT f (f i) = true) (v : GNode m) : label S M f v i = if v = .top (f i) ∨ Up S M f (.top (f i)) v = true then !S i else S i := by
  simp [label, hc]

/-- The label of the coalescent node on its own component is the ancestral sequence. -/
theorem Std.label_top_self {i : Fin m} (hc : isNT f (f i) = true) : label S M f (.top (f i)) i = S i :=
  label_of_not hc (by simp) fun _ _ => hs.not_up_part_top hc

/-- **On the other components, a node of a gall has the labels of its coalescent node** (Lemma 2.1 of the source). -/
theorem Std.label_part_off {c : Fin m} (hc : isNT f c = true) {σ : Row m} (hσ : σ ∈ rowsOf S M f c) {i : Fin m} (hi : f i ≠ c) : label S M f (.part c σ) i = label S M f (.top c) i := by
  have hvp : Valid S M f (.part c σ) := ⟨hc, hσ⟩
  have hvt : Valid S M f (.top c) := exists_of_isNT hc
  have htp := hs.top_up_part hc hσ
  have hvo : ∀ σ', (GNode.part c σ : GNode m) ≠ .part (f i) σ' := fun σ' h => hi (GNode.part.inj h).1.symm
  by_cases hc₁ : isNT f (f i) = true
  · by_cases hex : ∃ τ ∈ rowsOf S M f (f i), Up S M f (.part (f i) τ) (.top c) = true
    · obtain ⟨τ, hτ, hup⟩ := hex
      rw [hs.label_of_up hc₁ hτ hvp hvo (up_trans hup htp), hs.label_of_up hc₁ hτ hvt (by simp) hup]
    · push Not at hex
      rw [label_of_not hc₁ hvo fun τ hτ => ?_, label_of_not hc₁ (by simp) fun τ hτ => by simpa using hex τ hτ]
      refine Bool.eq_false_iff.2 fun h => hex τ hτ ?_
      refine hs.up_top_of_up_part hc hσ (show Valid S M f (.part (f i) τ) from ⟨hc₁, hτ⟩) (by simp) (fun τ' h' => hi (GNode.part.inj h').1) h
  · rw [label_trivial hc₁, label_trivial hc₁]
    have hk : Valid S M f (.top (f i)) := ⟨i, rfl⟩
    have hiff : Up S M f (.top (f i)) (.part c σ) = true ↔ Up S M f (.top (f i)) (.top c) = true :=
      ⟨fun h => hs.up_top_of_up_part hc hσ hk (by simp [hi]) (by simp) h, fun h => up_trans h htp⟩
    have h₁ : (GNode.part c σ : GNode m) ≠ .top (f i) := by simp
    have h₂ : (GNode.top c : GNode m) ≠ .top (f i) := by simpa using Ne.symm hi
    simp only [h₁, h₂, false_or, hiff]

/-- **Along a tree arc**, the label changes at the sites of the arc. -/
theorem Std.label_tree_arc {v u : GNode m} (hv : Valid S M f v) (hu : Valid S M f u) (hnp : ∀ c σ, v ≠ .part c σ) (hup : Up S M f u v = true)
    (hlow : ∀ u', Valid S M f u' → Up S M f u' v = true → u' = u ∨ Up S M f u' u = true) (i : Fin m) (ar : Fin m → Arr m) (hsite : isNT f (f i) = true → siteNode S f ar i ≠ v) :
    label S M f v i = if siteNode S f ar i = v then !label S M f u i else label S M f u i := by
  by_cases hc : isNT f (f i) = true
  · rw [ite_eq_right (hsite hc)]
    by_cases hex : ∃ τ ∈ rowsOf S M f (f i), Up S M f (.part (f i) τ) v = true
    · obtain ⟨τ, hτ, hτv⟩ := hex
      rw [hs.label_of_up hc hτ hv (fun σ => hnp _ σ) hτv]
      rcases hlow _ (show Valid S M f (.part (f i) τ) from ⟨hc, hτ⟩) hτv with rfl | h
      · exact (label_part_self hc τ).symm
      · by_cases hown : ∃ σ, u = .part (f i) σ
        · obtain ⟨σ, rfl⟩ := hown
          have hσ : σ ∈ rowsOf S M f (f i) := hu.2
          rw [not_up_part_part hσ] at h
          exact absurd h (by simp)
        · push Not at hown
          exact (hs.label_of_up hc hτ hu hown h).symm
    · push Not at hex
      rw [label_of_not hc (fun σ => hnp _ σ) fun τ hτ => by simpa using hex τ hτ]
      by_cases hown : ∃ σ, u = .part (f i) σ
      · obtain ⟨σ, rfl⟩ := hown
        exact absurd hup (hex σ hu.2)
      · push Not at hown
        exact (label_of_not hc hown fun τ hτ => Bool.eq_false_iff.2 fun h => hex τ hτ (up_trans h hup)).symm
  · rw [label_trivial hc, label_trivial hc]
    have hs₁ : siteNode S f ar i = .top (f i) := by simp [siteNode, hc]
    rw [hs₁]
    by_cases hvt : v = .top (f i)
    · have hun : ¬ (u = .top (f i) ∨ Up S M f (.top (f i)) u = true) := by
        rintro (rfl | h)
        · rw [hvt, up_irrefl] at hup
          exact absurd hup (by simp)
        · rw [hvt] at hup
          have h' := up_trans h hup
          rw [up_irrefl] at h'
          exact absurd h' (by simp)
      simp [hvt, hun]
    · have hiff : (v = .top (f i) ∨ Up S M f (.top (f i)) v = true) ↔ (u = .top (f i) ∨ Up S M f (.top (f i)) u = true) := by
        constructor
        · rintro (h | h)
          · exact absurd h hvt
          · rcases hlow _ (show Valid S M f (.top (f i)) from ⟨i, rfl⟩) h with h' | h'
            · exact Or.inl h'.symm
            · exact Or.inr h'
        · rintro (rfl | h)
          · exact Or.inr hup
          · exact Or.inr (up_trans h hup)
      have hne : (GNode.top (f i) : GNode m) ≠ v := fun h => hvt h.symm
      simp only [hne, ite_false]
      by_cases h' : u = .top (f i) ∨ Up S M f (.top (f i)) u = true
      · rw [ite_eq_left (hiff.2 h'), ite_eq_left h']
      · rw [ite_eq_right (fun h'' => h' (hiff.1 h'')), ite_eq_right h']

end Labels

/-! ### The network -/

section Net

variable {ar : Fin m → Arr m} (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c))

include hs har

omit hs in
/-- The first row of the chain with a site is below the arc of the site. -/
theorem siteNode_spec {i : Fin m} (hc : isNT f (f i) = true) :
    ∃ z, siteNode S f ar i = .part (f i) z ∧ z i ≠ S i ∧ ((z ∈ (ar (f i)).2.1 ∧ ∀ a ∈ (ar (f i)).2.1, a i ≠ S i → Sub1 S z a) ∨ (z ∈ (ar (f i)).2.2 ∧ ∀ a ∈ (ar (f i)).2.2, a i ≠ S i → Sub1 S z a)) := by
  have hA := har _ hc
  obtain ⟨y₀, hy₀, hy₀i⟩ : ∃ y ∈ (ar (f i)).2.1 ++ (ar (f i)).2.2, y i ≠ S i := by
    rcases hA.cover i rfl with ⟨y, hy, h⟩ | ⟨y, hy, h⟩
    · exact ⟨y, List.mem_append_left _ hy, h⟩
    · exact ⟨y, List.mem_append_right _ hy, h⟩
  have hmem : y₀ ∈ ((ar (f i)).2.1 ++ (ar (f i)).2.2).filter fun y => y i != S i := List.mem_filter.2 ⟨hy₀, by simpa using hy₀i⟩
  have hnone : (((ar (f i)).2.1 ++ (ar (f i)).2.2).filter fun y => y i != S i).argmin (card1 S) ≠ none := by
    rw [Ne, List.argmin_eq_none]
    intro h
    rw [h] at hmem
    simp at hmem
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hnone
  obtain ⟨hzm, hzi⟩ := List.mem_filter.1 (List.argmin_mem hz)
  have hzi' : z i ≠ S i := by simpa using hzi
  have hle : ∀ a ∈ (ar (f i)).2.1 ++ (ar (f i)).2.2, a i ≠ S i → card1 S z ≤ card1 S a := fun a ha hai =>
    List.le_of_mem_argmin (List.mem_filter.2 ⟨ha, by simpa using hai⟩) hz
  have hsn : siteNode S f ar i = .part (f i) z := by
    unfold siteNode
    rw [ite_eq_left hc, hz]
  refine ⟨z, hsn, hzi', ?_⟩
  rcases List.mem_append.1 hzm with h | h
  · exact Or.inl ⟨h, fun a ha hai => hA.chX.sub_of_le h ha (hle a (List.mem_append_left _ ha) hai)⟩
  · exact Or.inr ⟨h, fun a ha hai => hA.chY.sub_of_le h ha (hle a (List.mem_append_right _ ha) hai)⟩

omit hs har in
theorem endNode_valid {c : Fin m} (hc : isNT f c = true) {X : List (Row m)} (hX : Ch S X) (hrows : ∀ y ∈ X, y ∈ rowsOf S M f c) : Valid S M f (endNode S c X) := by
  rcases endNode_spec hX c with ⟨-, h⟩ | ⟨y, hy, h, -⟩
  · rw [h]
    exact exists_of_isNT hc
  · rw [h]
    exact ⟨hc, hrows y hy⟩

/-- The parent of a node is a node. -/
theorem par_valid {v u : GNode m} (hv : Valid S M f v) (h : par S M f ar v = some u) : Valid S M f u := by
  cases v with
  | root => simp [par] at h
  | top c =>
    obtain ⟨u', hu', hv', -⟩ := hs.treePar_spec hv (by simp)
    have : treePar S M f (.top c) = some u := h
    rw [hu'] at this
    rwa [← Option.some.inj this]
  | leaf ρ =>
    obtain ⟨u', hu', hv', -⟩ := hs.treePar_spec hv (by simp)
    have : treePar S M f (.leaf ρ) = some u := h
    rw [hu'] at this
    rwa [← Option.some.inj this]
  | part c σ =>
    have hA := har c hv.1
    simp only [par] at h
    split_ifs at h with h₁ h₂
    · rw [← Option.some.inj h]
      exact endNode_valid hv.1 hA.chX fun y hy => (hA.X_mem y hy).1
    · rw [← Option.some.inj h]
      exact endNode_valid hv.1 (hA.chX.filter _) fun y hy => (hA.X_mem y (List.mem_filter.1 hy).1).1
    · rw [← Option.some.inj h]
      exact endNode_valid hv.1 (hA.chY.filter _) fun y hy => (hA.Y_mem y (List.mem_filter.1 hy).1).1

omit hs in
theorem par₂_valid {v u : GNode m} (hv : Valid S M f v) (h : par₂ S ar v = some u) : Valid S M f u := by
  cases v with
  | part c σ =>
    have hA := har c hv.1
    simp only [par₂] at h
    split_ifs at h
    rw [← Option.some.inj h]
    exact endNode_valid hv.1 hA.chY fun y hy => (hA.Y_mem y hy).1
  | root => simp [par₂] at h
  | top c => simp [par₂] at h
  | leaf ρ => simp [par₂] at h

omit hs in
theorem site_valid (i : Fin m) : Valid S M f (siteNode S f ar i) := by
  by_cases hc : isNT f (f i) = true
  · obtain ⟨z, h, -, hz⟩ := siteNode_spec (ar := ar) har hc
    rw [h]
    refine ⟨hc, ?_⟩
    rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩
    · exact ((har _ hc).X_mem z hz).1
    · exact ((har _ hc).Y_mem z hz).1
  · have : siteNode S f ar i = .top (f i) := by simp [siteNode, hc]
    rw [this]
    exact ⟨i, rfl⟩

/-- **A step along a chain of a gall.** -/
theorem label_chain_step {c : Fin m} (hc : isNT f c = true) {X : List (Row m)} (hch : Ch S X) (hrows : ∀ y ∈ X, y ∈ rowsOf S M f c) {σ : Row m} (hσ : σ ∈ X)
    (hsp : ∀ i, f i = c → σ i ≠ S i → ∃ z, siteNode S f ar i = .part c z ∧ z ∈ X ∧ z i ≠ S i ∧ ∀ a ∈ X, a i ≠ S i → Sub1 S z a) (i : Fin m) :
    label S M f (.part c σ) i = if siteNode S f ar i = .part c σ then !label S M f (predNode S c X σ) i else label S M f (predNode S c X σ) i := by
  have hσr := hrows σ hσ
  have hb₁ : ∀ {u v w : Bool}, u ≠ w → v = w → u = !v := by decide
  have hb₂ : ∀ {u v w : Bool}, u ≠ w → v ≠ w → u = v := by decide
  by_cases hi : f i = c
  · subst hi
    have hne : ∀ {τ : Row m}, siteNode S f ar i = .part (f i) τ → τ i ≠ S i := by
      intro τ hτ
      by_cases hcc : isNT f (f i) = true
      · obtain ⟨z, h, hz, -⟩ := siteNode_spec (ar := ar) har hcc
        rw [h] at hτ
        rwa [← (GNode.part.inj hτ).2]
      · exact absurd hc hcc
    rw [label_part_self hc]
    rcases predNode_spec (S := S) hch (f i) hσ with ⟨h₁, h₂⟩ | ⟨y, hy, h₁, h₂, h₃, -, h₄⟩
    · rw [h₁, hs.label_top_self hc]
      by_cases hσi : σ i ≠ S i
      · obtain ⟨z, h₅, hz, hzi, h₆⟩ := hsp i rfl hσi
        obtain rfl := h₂ z hz (h₆ σ hσ hσi)
        rw [ite_eq_left h₅]
        exact hb₁ hσi rfl
      · push Not at hσi
        rw [ite_eq_right fun h => hne h hσi, hσi]
    · rw [h₁, label_part_self hc]
      by_cases hσi : σ i ≠ S i
      · obtain ⟨z, h₅, hz, hzi, h₆⟩ := hsp i rfl hσi
        by_cases hyi : y i ≠ S i
        · have hzσ : z ≠ σ := by
            rintro rfl
            exact h₃ (eq_of_sub1 h₂ (h₆ y hy hyi))
          have hne' : siteNode S f ar i ≠ .part (f i) σ := by
            rw [h₅]
            intro h'
            exact hzσ (GNode.part.inj h').2
          rw [ite_eq_right hne']
          exact hb₂ hσi hyi
        · push Not at hyi
          have hzσ : z = σ := by
            by_contra hne'
            exact h₄ z hz (h₆ σ hσ hσi) hne' i hzi hyi
          rw [ite_eq_left (by rw [h₅, hzσ])]
          exact hb₁ hσi hyi
      · push Not at hσi
        have hyi : y i = S i := by
          by_contra h'
          exact h₂ i h' hσi
        rw [ite_eq_right fun h => hne h hσi, hσi, hyi]
  · have hne' : siteNode S f ar i ≠ .part c σ := by
      unfold siteNode
      split_ifs
      · split
        · intro h
          exact hi (GNode.part.inj h).1
        · simp
      · simp
    rw [ite_eq_right hne', hs.label_part_off hc hσr hi]
    rcases predNode_spec (S := S) hch c hσ with ⟨h₁, -⟩ | ⟨y, hy, h₁, -⟩
    · rw [h₁]
    · rw [h₁, hs.label_part_off hc (hrows y hy) hi]

omit har in
/-- The rows of the chains, on their component, are the end of the chain. -/
theorem label_endNode {c : Fin m} (hc : isNT f c = true) {X : List (Row m)} (hch : Ch S X) (hrows : ∀ y ∈ X, y ∈ rowsOf S M f c) (i : Fin m) :
    label S M f (endNode S c X) i = if f i = c then topAt S X i else label S M f (.top c) i := by
  rcases endNode_spec (S := S) hch c with ⟨h₁, h₂⟩ | ⟨y, hy, h₂, h₃⟩
  · rw [h₂]
    by_cases hi : f i = c
    · subst hi
      rw [ite_eq_left rfl, hs.label_top_self hc, h₁, topAt_nil]
    · rw [ite_eq_right hi]
  · rw [h₂]
    by_cases hi : f i = c
    · subst hi
      rw [ite_eq_left rfl, label_part_self hc, topAt_eq_of_max hy h₃]
    · rw [ite_eq_right hi, hs.label_part_off hc (hrows y hy) hi]

/-- The number of nodes above a node. -/
def numAbove (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (v : GNode m) : ℕ := ((cands S M f).filter fun u => Up S M f u v).length

/-- The place of a node on its gall. -/
def galPos (S : Row m) (ar : Fin m → Arr m) (m' : ℕ) : GNode m → ℕ
  | .part c σ => if σ = (ar c).1 then m' + 1 else card1 S σ
  | _ => 0

omit hs har in
theorem numAbove_lt {u v : GNode m} (hu : Valid S M f u) (hul : ∀ ρ, u ≠ .leaf ρ) (h : Up S M f u v = true) : numAbove S M f u < numAbove S M f v :=
  length_filter_lt (fun _ _ hk => up_trans hk h) ⟨u, mem_cands_of_valid hu hul, h, up_irrefl⟩

omit har in
/-- The nodes of a gall have the same nodes above. -/
theorem numAbove_part {c : Fin m} (hc : isNT f c = true) {σ τ : Row m} (hσ : σ ∈ rowsOf S M f c) (hτ : τ ∈ rowsOf S M f c) : numAbove S M f (.part c σ) = numAbove S M f (.part c τ) := by
  have hkey : ∀ {σ τ : Row m}, σ ∈ rowsOf S M f c → τ ∈ rowsOf S M f c → ∀ k ∈ cands S M f, Up S M f k (.part c σ) = true → Up S M f k (.part c τ) = true := by
    intro σ τ hσ hτ k hk h
    by_cases h₁ : k = .top c
    · rw [h₁]
      exact hs.top_up_part hc hτ
    by_cases h₂ : ∃ ρ, k = .part c ρ
    · obtain ⟨ρ, rfl⟩ := h₂
      rw [not_up_part_part hσ] at h
      exact absurd h (by simp)
    · push Not at h₂
      exact up_trans (hs.up_top_of_up_part hc hσ (valid_of_mem_cands hk) h₁ h₂ h) (hs.top_up_part hc hτ)
  refine le_antisymm (length_filter_le' fun k hk h => hkey hσ hτ k hk h) (length_filter_le' fun k hk h => hkey hτ hσ k hk h)

/-- **The network is acyclic**: the number of nodes above goes up along an arc, and along a gall the place on it does. -/
theorem rank_lt {a b : GNode m} (hb : Valid S M f b) (h : par S M f ar b = some a ∨ par₂ S ar b = some a) :
    numAbove S M f a * (m + 2) + galPos S ar m a < numAbove S M f b * (m + 2) + galPos S ar m b := by
  have hposle : ∀ v : GNode m, galPos S ar m v ≤ m + 1 := by
    intro v
    cases v with
    | part c σ =>
      simp only [galPos]
      split_ifs
      · exact le_rfl
      · have : card1 S σ ≤ (List.finRange m).length := List.length_filter_le _ _
        simp only [List.length_finRange] at this
        omega
    | root => simp [galPos]
    | top c => simp [galPos]
    | leaf ρ => simp [galPos]
  -- when `a` is above `b`
  have hup' : ∀ {a b : GNode m}, (∀ ρ, a ≠ .leaf ρ) → Valid S M f a → Up S M f a b = true → numAbove S M f a * (m + 2) + galPos S ar m a < numAbove S M f b * (m + 2) + galPos S ar m b := by
    intro a b hl ha hab
    have h₁ := numAbove_lt ha hl hab
    have h₂ : (numAbove S M f a + 1) * (m + 2) ≤ numAbove S M f b * (m + 2) := Nat.mul_le_mul_right _ h₁
    have h₃ := hposle a
    nlinarith
  cases b with
  | root => simp [par, par₂] at h
  | top c =>
    simp only [par₂, reduceCtorEq, or_false] at h
    obtain ⟨u', hu', hv', hl, hup'', -⟩ := hs.treePar_spec hb (by simp)
    have heq : a = u' := Option.some.inj ((show treePar S M f (.top c) = some a from h).symm.trans hu')
    subst heq
    exact hup' hl hv' hup''
  | leaf ρ =>
    simp only [par₂, reduceCtorEq, or_false] at h
    obtain ⟨u', hu', hv', hl, hup'', -⟩ := hs.treePar_spec hb (by simp)
    have heq : a = u' := Option.some.inj ((show treePar S M f (.leaf ρ) = some a from h).symm.trans hu')
    subst heq
    exact hup' hl hv' hup''
  | part c σ =>
    have hA := har c hb.1
    have hend : ∀ {X : List (Row m)}, Ch S X → (∀ y ∈ X, y ∈ rowsOf S M f c ∧ y ≠ (ar c).1) → (∀ y ∈ X, galPos S ar m (.part c y) < galPos S ar m (.part c σ)) → a = endNode S c X →
        numAbove S M f a * (m + 2) + galPos S ar m a < numAbove S M f (.part c σ) * (m + 2) + galPos S ar m (.part c σ) := by
      intro X hch hrows hlt hae
      rcases endNode_spec (S := S) hch c with ⟨-, h₁⟩ | ⟨y, hy, h₁, -⟩
      · rw [hae, h₁]
        exact hup' (by simp) (exists_of_isNT hb.1) (hs.top_up_part hb.1 hb.2)
      · rw [hae, h₁, numAbove_part hs hb.1 (hrows y hy).1 hb.2]
        have := hlt y hy
        omega
    have hcard : ∀ y : Row m, card1 S y ≤ m := fun y => by
      have : card1 S y ≤ (List.finRange m).length := List.length_filter_le _ _
      simpa using this
    have hpos : ∀ {y : Row m}, y ≠ (ar c).1 → galPos S ar m (.part c y) = card1 S y := fun {y} hy => by simp [galPos, hy]
    simp only [par, par₂] at h
    by_cases hσ : σ = (ar c).1
    · have hposσ : galPos S ar m (.part c σ) = m + 1 := by simp [galPos, hσ]
      simp only [hσ, ite_true, Option.some.injEq] at h
      rcases h with h | h
      · refine hend hA.chX hA.X_mem (fun y hy => ?_) h.symm
        rw [hposσ, hpos (hA.X_mem y hy).2]
        have := hcard y
        omega
      · refine hend hA.chY hA.Y_mem (fun y hy => ?_) h.symm
        rw [hposσ, hpos (hA.Y_mem y hy).2]
        have := hcard y
        omega
    · have hposσ := hpos hσ
      simp only [hσ, ite_false, reduceCtorEq, or_false] at h
      split_ifs at h with hσX
      · refine hend (hA.chX.filter _) (fun y hy => hA.X_mem y (List.mem_filter.1 hy).1) (fun y hy => ?_) (Option.some.inj h).symm
        rw [hposσ, hpos (hA.X_mem y (List.mem_filter.1 hy).1).2]
        simpa using (List.mem_filter.1 hy).2
      · refine hend (hA.chY.filter _) (fun y hy => hA.Y_mem y (List.mem_filter.1 hy).1) (fun y hy => ?_) (Option.some.inj h).symm
        rw [hposσ, hpos (hA.Y_mem y (List.mem_filter.1 hy).1).2]
        simpa using (List.mem_filter.1 hy).2

omit har in
/-- A node other than the root has a parent. -/
theorem exists_par {v : GNode m} (hv : Valid S M f v) (hne : v ≠ .root) : ∃ u, par S M f ar v = some u := by
  cases v with
  | root => exact absurd rfl hne
  | top c =>
    obtain ⟨u, hu, -⟩ := hs.treePar_spec hv hne
    exact ⟨u, hu⟩
  | leaf ρ =>
    obtain ⟨u, hu, -⟩ := hs.treePar_spec hv hne
    exact ⟨u, hu⟩
  | part c σ =>
    simp only [par]
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

omit hs in
/-- The two ends of the chains of a gall are different nodes. -/
theorem endNode_ne {c : Fin m} (hc : isNT f c = true) : endNode S c (ar c).2.1 ≠ endNode S c (ar c).2.2 := by
  have hA := har c hc
  obtain ⟨k, hk⟩ := exists_of_isNT (f := f) hc
  rcases endNode_spec (S := S) hA.chX c with ⟨h₁, h₂⟩ | ⟨y, hy, h₂, -⟩ <;> rcases endNode_spec (S := S) hA.chY c with ⟨h₃, h₄⟩ | ⟨z, hz, h₄, -⟩
  · exfalso
    rcases hA.cover k hk with ⟨y, hy, -⟩ | ⟨y, hy, -⟩
    · rw [h₁] at hy
      simp at hy
    · rw [h₃] at hy
      simp at hy
  · rw [h₂, h₄]
    simp
  · rw [h₂, h₄]
    simp
  · rw [h₂, h₄]
    intro h
    obtain rfl : y = z := (GNode.part.inj h).2
    have hyS := (mem_rowsOf.1 (hA.X_mem y hy).1).2
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ S i := by
      by_contra hno
      push Not at hno
      exact hyS (funext hno)
    exact hi (hA.disj y hy y hz i hi)

/-- **The labels along an arc that isn't into a recombination node.** -/
theorem label_step_all {v p : GNode m} (hv : Valid S M f v) (hp : par S M f ar v = some p) (hq : par₂ S ar v = none) (i : Fin m) :
    label S M f v i = if siteNode S f ar i = v then !label S M f p i else label S M f p i := by
  have htree : ∀ v, (∀ c σ, v ≠ GNode.part c σ) → Valid S M f v → v ≠ .root → treePar S M f v = some p → label S M f v i = if siteNode S f ar i = v then !label S M f p i else label S M f p i := by
    intro v hnp hv hne h
    obtain ⟨u, hu, hvu, -, hup, hlow⟩ := hs.treePar_spec hv hne
    obtain rfl : p = u := Option.some.inj (h.symm.trans hu)
    refine hs.label_tree_arc hv hvu hnp hup hlow i ar fun hc => ?_
    obtain ⟨z, hz, -⟩ := siteNode_spec (ar := ar) har hc
    rw [hz]
    exact (hnp _ _ · |>.elim) ∘ Eq.symm
  cases v with
  | root => simp [par] at hp
  | top c => exact htree _ (by simp) hv (by simp) hp
  | leaf ρ => exact htree _ (by simp) hv (by simp) hp
  | part c σ =>
    have hA := har c hv.1
    have hσs : σ ≠ (ar c).1 := by
      intro h
      simp [par₂, h] at hq
    simp only [par, hσs, ite_false] at hp
    have hsp : ∀ {X X' : List (Row m)}, ((X = (ar c).2.1 ∧ X' = (ar c).2.2) ∨ (X = (ar c).2.2 ∧ X' = (ar c).2.1)) → σ ∈ X → ∀ i, f i = c → σ i ≠ S i → ∃ z, siteNode S f ar i = .part c z ∧ z ∈ X ∧ z i ≠ S i ∧ ∀ a ∈ X, a i ≠ S i → Sub1 S z a := by
      intro X X' hXX hσX i hi hσi
      subst hi
      obtain ⟨z, h₁, h₂, h₃⟩ := siteNode_spec (ar := ar) har hv.1
      refine ⟨z, h₁, ?_, h₂, ?_⟩
      · rcases hXX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases h₃ with ⟨h₄, -⟩ | ⟨h₄, -⟩
          · exact h₄
          · exact absurd (hA.disj σ hσX z h₄ i hσi) h₂
        · rcases h₃ with ⟨h₄, -⟩ | ⟨h₄, -⟩
          · exact absurd (hA.disj z h₄ σ hσX i h₂) hσi
          · exact h₄
      · rcases hXX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases h₃ with ⟨-, h₄⟩ | ⟨h₄, -⟩
          · exact h₄
          · exact absurd (hA.disj σ hσX z h₄ i hσi) h₂
        · rcases h₃ with ⟨h₄, -⟩ | ⟨-, h₄⟩
          · exact absurd (hA.disj z h₄ σ hσX i h₂) hσi
          · exact h₄
    split_ifs at hp with hσX
    · rw [← Option.some.inj hp]
      exact label_chain_step hs har hv.1 hA.chX (fun y hy => (hA.X_mem y hy).1) hσX (hsp (Or.inl ⟨rfl, rfl⟩) hσX) i
    · have hσY : σ ∈ (ar c).2.2 := by
        rcases hA.all σ hv.2 with h | h | h
        · exact absurd h hσs
        · exact absurd h hσX
        · exact h
      rw [← Option.some.inj hp]
      exact label_chain_step hs har hv.1 hA.chY (fun y hy => (hA.Y_mem y hy).1) hσY (hsp (Or.inr ⟨rfl, rfl⟩) hσY) i

/-- **The recombination node.** Its label is that of the end of the second chain before the recombination point, and of the first after. -/
theorem label_recomb_all {c : Fin m} (hc : isNT f c = true) : ∃ n, ∀ i, label S M f (.part c (ar c).1) i = if i.val < n then label S M f (endNode S c (ar c).2.2) i else label S M f (endNode S c (ar c).2.1) i := by
  have hA := har c hc
  obtain ⟨n, hn⟩ := hA.point
  refine ⟨n, fun i => ?_⟩
  rw [label_endNode hs hc hA.chY (fun y hy => (hA.Y_mem y hy).1), label_endNode hs hc hA.chX (fun y hy => (hA.X_mem y hy).1)]
  by_cases hi : f i = c
  · subst hi
    rw [label_part_self hc, hn i rfl, ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right hi, ite_eq_right hi, hs.label_part_off hc hA.s_mem hi]
    split_ifs <;> rfl

omit har in
/-- The label of a leaf is its row. -/
theorem label_leaf {r : Row m} (hr : r ∈ M) (i : Fin m) : label S M f (.leaf r) i = r i := by
  have hv : Valid S M f (.leaf r) := hr
  have hmk : mkRow S f (f i) r i = r i := by simp [mkRow]
  by_cases hc : isNT f (f i) = true
  · by_cases hne : mkRow S f (f i) r = S
    · rw [label_of_not hc (by simp) fun τ hτ => Bool.eq_false_iff.2 fun h => ?_]
      · rw [← hmk, hne]
      · have := cl_part.1 ((up_iff.1 h).2.1 r hr (cl_leaf.2 rfl))
        exact (mem_rowsOf.1 hτ).2 (this.symm.trans hne)
    · have hτ : mkRow S f (f i) r ∈ rowsOf S M f (f i) := mem_rowsOf.2 ⟨⟨r, hr, rfl⟩, hne⟩
      rw [hs.label_of_up hc hτ hv (by simp) (up_iff.2 ⟨by simp, fun r' _ h' => ?_, fun _ => Or.inl (by simp [GNode.rank])⟩), hmk]
      rw [cl_leaf.1 h']
      exact cl_part.2 rfl
  · rw [label_trivial hc]
    have hsingle : ∀ j, f j = f i → j = i := by
      intro j hj
      have hlen : ¬ 1 < (sitesOf f (f i)).length := by simpa [isNT] using hc
      have hnd : (sitesOf f (f i)).Nodup := (List.nodup_finRange m).filter _
      rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff] at hlen
      push Not at hlen
      exact hlen j i (by simp [sitesOf, hj]) (by simp [sitesOf])
    have hup : Up S M f (.top (f i)) (.leaf r) = true ↔ r i ≠ S i := by
      constructor
      · intro h
        obtain ⟨j, hj, hrj⟩ := mk_ne_iff.1 (cl_top.1 ((up_iff.1 h).2.1 r hr (cl_leaf.2 rfl)))
        rwa [hsingle j hj] at hrj
      · intro h
        refine up_iff.2 ⟨by simp, fun r' _ h' => ?_, fun _ => Or.inl ?_⟩
        · rw [cl_leaf.1 h']
          exact cl_top.2 (mk_ne_iff.2 ⟨i, rfl, h⟩)
        · have h₁ : (GNode.top (f i) : GNode m).rank f ≤ 3 := by
            simp only [GNode.rank]
            split_ifs
            omega
          have h₂ : (GNode.leaf r : GNode m).rank f = 4 := rfl
          omega
    have hb : ∀ {u v : Bool}, u ≠ v → (!v) = u := by decide
    by_cases hri : r i ≠ S i
    · rw [ite_eq_left (Or.inr (hup.2 hri))]
      exact hb hri
    · push Not at hri
      rw [ite_eq_right, hri]
      rintro (h | h)
      · simp at h
      · exact absurd hri (hup.1 h)

omit hs har in
/-- The label of the root is the ancestral sequence. -/
theorem label_root (i : Fin m) : label S M f .root i = S i := by
  have hnot : ∀ {u : GNode m}, u.rank f ≠ 0 → Up S M f u .root = false := by
    intro u hu
    refine Bool.eq_false_iff.2 fun h => ?_
    obtain ⟨-, -, h₂⟩ := up_iff.1 h
    have ht := h₂ fun _ _ _ => rfl
    have hr : (GNode.root : GNode m).rank f = 0 := rfl
    unfold Tie at ht
    rw [hr] at ht
    omega
  by_cases hc : isNT f (f i) = true
  · exact label_of_not hc (by simp) fun τ _ => hnot (by simp [GNode.rank])
  · rw [label_trivial hc, ite_eq_right]
    rintro (h | h)
    · simp at h
    · rw [hnot (by have := rank_top_ge (f := f) (c := f i); omega)] at h
      exact absurd h (by simp)

end Net

/-! ### The network as a `PreNet` -/

section Assemble

open Gusfield2007.Network

variable {ar : Fin m → Arr m} (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c))

/-- The nodes as a type. -/
abbrev VNode (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : Type := {v : GNode m // Valid S M f v}

/-- An option of a node, on the nodes as a type. -/
def liftOpt {o : Option (GNode m)} (h : ∀ u, o = some u → Valid S M f u) : Option (VNode S M f) := o.pmap Subtype.mk h

theorem liftOpt_eq_some {o : Option (GNode m)} {h : ∀ u, o = some u → Valid S M f u} {q : VNode S M f} : liftOpt h = some q ↔ o = some q.1 := by
  cases o with
  | none => simp [liftOpt]
  | some a =>
    simp only [liftOpt, Option.pmap_some, Option.some.injEq]
    exact ⟨fun h' => by rw [← h'], fun h' => Subtype.ext h'⟩

theorem liftOpt_eq_none {o : Option (GNode m)} {h : ∀ u, o = some u → Valid S M f u} : liftOpt h = none ↔ o = none := by
  cases o <;> simp [liftOpt]

/-- The second parent is the end of the second chain, at the recombination node. -/
theorem par₂_some {v q : GNode m} (hv : Valid S M f v) (h : par₂ S ar v = some q) : ∃ c, isNT f c = true ∧ v = .part c (ar c).1 ∧ q = endNode S c (ar c).2.2 := by
  cases v with
  | part c σ =>
    simp only [par₂] at h
    split_ifs at h with h₁
    exact ⟨c, hv.1, by rw [h₁], (Option.some.inj h).symm⟩
  | root => simp [par₂] at h
  | top c => simp [par₂] at h
  | leaf ρ => simp [par₂] at h

theorem par_recomb {c : Fin m} : par S M f ar (.part c (ar c).1) = some (endNode S c (ar c).2.1) := by
  simp [par]

theorem par₂_recomb {c : Fin m} : par₂ S ar (.part c (ar c).1) = some (endNode S c (ar c).2.2) := by
  simp [par₂]

/-- **The reduced galled tree** as a `PreNet`: the nodes, the parents, the sites and the labels are the functions of the algorithm. -/
def gPreNet : PreNet (Fin m) (VNode S M f) where
  root := ⟨.root, trivial⟩
  par v := liftOpt (o := par S M f ar v.1) fun _ hu => par_valid hs har v.2 hu
  par₂ v := liftOpt (o := par₂ S ar v.1) fun _ hu => par₂_valid har v.2 hu
  site i := some ⟨siteNode S f ar i, site_valid har i⟩
  label v := label S M f v.1
  par_eq_none v := by
    rw [liftOpt_eq_none]
    constructor
    · intro h
      by_contra hne
      obtain ⟨u, hu⟩ := exists_par (ar := ar) hs v.2 fun h' => hne (Subtype.ext h')
      rw [hu] at h
      simp at h
    · intro h
      rw [h]
      rfl
  par₂_root := liftOpt_eq_none.2 rfl
  par₂_ne v q hq hp := by
    rw [liftOpt_eq_some] at hq hp
    obtain ⟨c, hc, hv, hq'⟩ := par₂_some v.2 hq
    rw [hv, par_recomb] at hp
    exact endNode_ne har hc ((Option.some.inj hp).trans hq')
  acyclic := Gusfield2007.acyclic_of_strict (fun v : VNode S M f => numAbove S M f v.1 * (m + 2) + galPos S ar m v.1) fun a b h => by
    refine rank_lt hs har b.2 ?_
    rcases h with h | h
    · exact Or.inl (liftOpt_eq_some.1 h)
    · exact Or.inr (liftOpt_eq_some.1 h)
  site_tree i v hv := by
    have hve : siteNode S f ar i = v.1 := congrArg Subtype.val (Option.some.inj hv)
    constructor
    · refine liftOpt_eq_none.2 ?_
      rw [← hve]
      by_cases hc : isNT f (f i) = true
      · obtain ⟨z, h, -, hz⟩ := siteNode_spec (ar := ar) har hc
        rw [h]
        have hzs : z ≠ (ar (f i)).1 := by
          rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩
          · exact ((har _ hc).X_mem z hz).2
          · exact ((har _ hc).Y_mem z hz).2
        simp [par₂, hzs]
      · simp [siteNode, hc, par₂]
    · intro hroot
      have hv₁ : v.1 = .root := congrArg Subtype.val hroot
      rw [hv₁] at hve
      by_cases hc : isNT f (f i) = true
      · obtain ⟨z, h, -⟩ := siteNode_spec (ar := ar) har hc
        rw [h] at hve
        simp at hve
      · simp [siteNode, hc] at hve
  label_tree v p hp hq i := by
    have h₁ := label_step_all hs har v.2 (liftOpt_eq_some.1 hp) (liftOpt_eq_none.1 hq) i
    by_cases hsv : siteNode S f ar i = v.1
    · rw [ite_eq_left hsv] at h₁
      rw [ite_eq_left (congrArg some (Subtype.ext hsv))]
      exact h₁
    · rw [ite_eq_right hsv] at h₁
      rw [ite_eq_right fun h' => hsv (congrArg Subtype.val (Option.some.inj h'))]
      exact h₁
  label_recomb v p q hp hq i := by
    obtain ⟨c, hc, hv, hq'⟩ := par₂_some v.2 (liftOpt_eq_some.1 hq)
    have hp' := liftOpt_eq_some.1 hp
    rw [hv, par_recomb] at hp'
    obtain ⟨n, hn⟩ := label_recomb_all hs har hc
    have hv' : label S M f v.1 i = if i.val < n then label S M f (endNode S c (ar c).2.2) i else label S M f (endNode S c (ar c).2.1) i := by
      rw [hv]
      exact hn i
    have hpe : p.1 = endNode S c (ar c).2.1 := (Option.some.inj hp').symm
    change label S M f v.1 i = label S M f p.1 i ∨ label S M f v.1 i = label S M f q.1 i
    rw [hv', hpe, hq']
    by_cases hi : i.val < n
    · rw [ite_eq_left hi]
      exact Or.inr rfl
    · rw [ite_eq_right hi]
      exact Or.inl rfl

/-- The network of the algorithm. -/
noncomputable def gNet : Gusfield2007.Network (Fin m) (VNode S M f) ({v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) :=
  (gPreNet hs har).toNetwork fun _ => ⟨_, rfl⟩

/-- An arc goes from a parent. -/
theorem gNet_arc (e : {v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) :
    par S M f ar ((gNet hs har).tgt e).1 = some ((gNet hs har).src e).1 ∨ par₂ S ar ((gNet hs har).tgt e).1 = some ((gNet hs har).src e).1 := by
  rcases e with v | v
  · have h₁ : (gPreNet hs har).par v.1 = some ((gNet hs har).src (.inl v)) := (Option.some_get _).symm
    exact Or.inl (liftOpt_eq_some.1 h₁)
  · have h₁ : (gPreNet hs har).par₂ v.1 = some ((gNet hs har).src (.inr v)) := (Option.some_get _).symm
    exact Or.inr (liftOpt_eq_some.1 h₁)

/-- A parent gives an arc. -/
theorem gNet_exists_arc {v : VNode S M f} {u : GNode m} (h : par S M f ar v.1 = some u ∨ par₂ S ar v.1 = some u) :
    ∃ e, ((gNet hs har).src e).1 = u ∧ (gNet hs har).tgt e = v := by
  rcases h with h | h
  · have hne : (gPreNet hs har).par v ≠ none := fun h' => by
      rw [liftOpt_eq_none.1 h'] at h
      simp at h
    refine ⟨.inl ⟨v, hne⟩, ?_, rfl⟩
    have h₁ : (gPreNet hs har).par v = some ((gNet hs har).src (.inl ⟨v, hne⟩)) := (Option.some_get _).symm
    exact Option.some.inj ((liftOpt_eq_some.1 h₁).symm.trans h)
  · have hne : (gPreNet hs har).par₂ v ≠ none := fun h' => by
      rw [liftOpt_eq_none.1 h'] at h
      simp at h
    refine ⟨.inr ⟨v, hne⟩, ?_, rfl⟩
    have h₁ : (gPreNet hs har).par₂ v = some ((gNet hs har).src (.inr ⟨v, hne⟩)) := (Option.some_get _).symm
    exact Option.some.inj ((liftOpt_eq_some.1 h₁).symm.trans h)

/-- A recombination node of the network is the row at the recombination node of a gall. -/
theorem gNet_isRecomb {x : VNode S M f} (hx : (gNet hs har).IsRecomb x) : ∃ c, isNT f c = true ∧ x.1 = .part c (ar c).1 := by
  obtain ⟨e, g, heg, he, hg⟩ := hx
  have hq : ∃ q, par₂ S ar x.1 = some q := by
    rcases e with e | e
    · rcases g with g | g
      · exact absurd (congrArg Sum.inl (Subtype.ext (he.trans hg.symm))) heg
      · have hg' : g.1 = x := hg
        exact Option.ne_none_iff_exists'.1 fun h' => g.2 (by rw [hg']; exact liftOpt_eq_none.2 h')
    · have he' : e.1 = x := he
      exact Option.ne_none_iff_exists'.1 fun h' => e.2 (by rw [he']; exact liftOpt_eq_none.2 h')
  obtain ⟨q, hq⟩ := hq
  obtain ⟨c, hc, hv, -⟩ := par₂_some x.2 hq
  exact ⟨c, hc, hv⟩

theorem gNet_label (v : VNode S M f) : (gNet hs har).label v = label S M f v.1 := rfl

/-- The network has the ancestral sequence. -/
theorem gNet_ancestral : (gNet hs har).ancestral = S := funext label_root

/-- The network has single crossovers. -/
theorem gNet_obeys : (gNet hs har).Obeys .single := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := gNet_isRecomb hs har hx
  obtain ⟨e, he₁, he₂⟩ := gNet_exists_arc hs har (v := x) (u := endNode S c (ar c).2.2) (Or.inr (by rw [hxc]; exact par₂_recomb))
  obtain ⟨g, hg₁, hg₂⟩ := gNet_exists_arc hs har (v := x) (u := endNode S c (ar c).2.1) (Or.inl (by rw [hxc]; exact par_recomb))
  obtain ⟨n, hn⟩ := label_recomb_all hs har hc
  have hne : e ≠ g := by
    rintro rfl
    exact endNode_ne har hc (hg₁.symm.trans he₁)
  let L₀ : LowerSet (Fin m) := ⟨{i | i.val < n}, fun a b hba ha => lt_of_le_of_lt (show b.val ≤ a.val from hba) ha⟩
  refine ⟨e, g, hne, he₂, hg₂, L₀, fun i => ?_⟩
  rw [gNet_label, gNet_label, gNet_label, he₁, hg₁, hxc, hn i]
  by_cases hi : i.val < n
  · have hi' : i ∈ L₀ := hi
    rw [ite_eq_left hi, ite_eq_left hi']
  · have hi' : i ∉ L₀ := hi
    rw [ite_eq_right hi, ite_eq_right hi']

theorem endNode_cases (c : Fin m) (X : List (Row m)) : endNode S c X = .top c ∨ ∃ y, endNode S c X = .part c y := by
  unfold endNode
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

include hs in
/-- A parent isn't a leaf. -/
theorem par_not_leaf {v u : GNode m} (hv : Valid S M f v) (h : par S M f ar v = some u ∨ par₂ S ar v = some u) (ρ : Row m) : u ≠ .leaf ρ := by
  have hend : ∀ {c : Fin m} {X : List (Row m)}, u = endNode S c X → u ≠ .leaf ρ := by
    rintro c X rfl
    rcases endNode_cases (S := S) c X with h' | ⟨y, h'⟩ <;> rw [h'] <;> simp
  rcases h with h | h
  · cases v with
    | root => simp [par] at h
    | top c =>
      obtain ⟨u', hu', -, hl, -⟩ := hs.treePar_spec hv (by simp)
      have heq : u = u' := Option.some.inj ((show treePar S M f (.top c) = some u from h).symm.trans hu')
      rw [heq]
      exact hl ρ
    | leaf r =>
      obtain ⟨u', hu', -, hl, -⟩ := hs.treePar_spec hv (by simp)
      have heq : u = u' := Option.some.inj ((show treePar S M f (.leaf r) = some u from h).symm.trans hu')
      rw [heq]
      exact hl ρ
    | part c σ =>
      simp only [par] at h
      split_ifs at h
      · exact hend (Option.some.inj h).symm
      · exact hend (Option.some.inj h).symm
      · exact hend (Option.some.inj h).symm
  · obtain ⟨c, -, -, hq⟩ := par₂_some hv h
    exact hend hq

include hs har in
/-- **A node that isn't a leaf has a child**: the next node on the way to a row below it. -/
theorem exists_child {v : GNode m} (hv : Valid S M f v) (hnl : ∀ ρ, v ≠ .leaf ρ) : ∃ w, Valid S M f w ∧ (par S M f ar w = some v ∨ par₂ S ar w = some v) := by
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  have hmem : (GNode.leaf r : GNode m) ∈ {w | Valid S M f w ∧ Up S M f v w = true ∧ w.cl S f r = true} := by
    refine ⟨hr, up_iff.2 ⟨hnl r, fun r' _ h' => ?_, fun _ => Or.inl ?_⟩, cl_leaf.2 rfl⟩
    · rw [cl_leaf.1 h']
      exact hrv
    · have hle := rank_le (f := f) v
      have hL : (GNode.leaf r : GNode m).rank f = 4 := rfl
      have hne4 : v.rank f ≠ 4 := by
        intro h4
        cases v with
        | root => simp [GNode.rank] at h4
        | leaf ρ => exact hnl ρ rfl
        | part _ _ => simp [GNode.rank] at h4
        | top c =>
          simp only [GNode.rank] at h4
          split_ifs at h4 <;> omega
      omega
  obtain ⟨w, ⟨hw, hvw, hrw⟩, hmin⟩ := (InvImage.wf (key S M f) Nat.lt_wfRel.wf).has_min _ ⟨_, hmem⟩
  have hlow : ∀ w', Valid S M f w' → Up S M f v w' = true → w'.cl S f r = true → ¬ key S M f w' < key S M f w := fun w' h₁ h₂ h₃ => hmin w' ⟨h₁, h₂, h₃⟩
  have htree : (∀ c σ, w ≠ GNode.part c σ) → w ≠ .root → par S M f ar w = treePar S M f w → ∃ w, Valid S M f w ∧ (par S M f ar w = some v ∨ par₂ S ar w = some v) := by
    intro _ hwr hpar
    obtain ⟨u, hu, hvu, -, hup, hl⟩ := hs.treePar_spec hw hwr
    refine ⟨w, hw, Or.inl ?_⟩
    rw [hpar, hu]
    rcases hl v hv hvw with h | h
    · rw [h]
    · exfalso
      exact hlow u hvu h ((up_iff.1 hup).2.1 r (by
        by_contra hrM
        exact hrM hr) hrw) (key_lt hup)
  cases w with
  | root =>
    exfalso
    obtain ⟨-, h₂, h₃⟩ := up_iff.1 hvw
    have ht := h₃ fun _ _ _ => rfl
    have hr₀ : (GNode.root : GNode m).rank f = 0 := rfl
    have hi₀ : (GNode.root : GNode m).idx = 0 := rfl
    unfold Tie at ht
    rw [hr₀, hi₀] at ht
    omega
  | top c => exact htree (by simp) (by simp) rfl
  | leaf ρ => exact htree (by simp) (by simp) rfl
  | part c τ =>
    have hτ : τ ∈ rowsOf S M f c := hw.2
    have hA := har c hw.1
    by_cases hvt : v = .top c
    · subst hvt
      -- the first node of the first chain, or the recombination node
      cases hX : (ar c).2.1.argmin (card1 S) with
      | none =>
        refine ⟨.part c (ar c).1, ⟨hw.1, hA.s_mem⟩, Or.inl ?_⟩
        rw [par_recomb, List.argmin_eq_none.1 hX]
        simp [endNode]
      | some y =>
        have hy := List.argmin_mem hX
        refine ⟨.part c y, ⟨hw.1, (hA.X_mem y hy).1⟩, Or.inl ?_⟩
        have hnil : ((ar c).2.1.filter fun z => decide (card1 S z < card1 S y)) = [] := by
          refine List.filter_eq_nil_iff.2 fun z hz hlt => ?_
          have := List.le_of_mem_argmin hz hX
          have hlt' : card1 S z < card1 S y := by simpa using hlt
          omega
        simp [par, (hA.X_mem y hy).2, hy, predNode, hnil, endNode]
    · have hvp : ∀ ρ, v ≠ .part c ρ := by
        rintro ρ rfl
        rw [not_up_part_part hτ] at hvw
        exact absurd hvw (by simp)
      exfalso
      have htv := hs.up_top_of_up_part hw.1 hτ hv hvt hvp hvw
      have htop := hs.top_up_part hw.1 hτ
      exact hlow (.top c) (exists_of_isNT hw.1) htv ((up_iff.1 htop).2.1 r hr hrw) (key_lt htop)

/-- The nodes of the gall of a component. -/
def InGall (c : Fin m) (v : GNode m) : Prop := v = .top c ∨ ∃ σ, v = .part c σ

theorem inGall_endNode (c : Fin m) (X : List (Row m)) : InGall c (endNode S c X) := by
  rcases endNode_cases (S := S) c X with h | ⟨y, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, h⟩

theorem InGall.unique {c c' : Fin m} {v : GNode m} (h : InGall c v) (h' : InGall c' v) : c = c' := by
  rcases h with rfl | ⟨σ, rfl⟩ <;> rcases h' with h' | ⟨τ, h'⟩
  · exact GNode.top.inj h'
  · simp at h'
  · simp at h'
  · exact (GNode.part.inj h').1

include hs har in
/-- Going back from a node of a gall, other than its coalescent node, stays on the gall. -/
theorem gNet_back {c : Fin m} (e : {v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) (h : InGall c ((gNet hs har).tgt e).1) (hne : ((gNet hs har).tgt e).1 ≠ .top c) : InGall c ((gNet hs har).src e).1 := by
  rcases h with h | ⟨σ, h⟩
  · exact absurd h hne
  have harc := gNet_arc hs har e
  rw [h] at harc
  rcases harc with h₁ | h₁
  · simp only [par] at h₁
    split_ifs at h₁
    · rw [← Option.some.inj h₁]
      exact inGall_endNode _ _
    · rw [← Option.some.inj h₁]
      exact inGall_endNode _ _
    · rw [← Option.some.inj h₁]
      exact inGall_endNode _ _
  · simp only [par₂] at h₁
    split_ifs at h₁
    rw [← Option.some.inj h₁]
    exact inGall_endNode _ _

/-- The measure that goes up along the arcs. -/
def rkN (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m) (v : GNode m) : ℕ := numAbove S M f v * (m + 2) + galPos S ar m v

include hs har in
theorem gNet_rk_lt (e : {v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) : rkN S M f ar ((gNet hs har).src e).1 < rkN S M f ar ((gNet hs har).tgt e).1 :=
  rank_lt hs har ((gNet hs har).tgt e).2 (gNet_arc hs har e)

include hs har in
theorem gNet_rk_le {a b : VNode S M f} (h : (gNet hs har).Reach a b) : rkN S M f ar a.1 ≤ rkN S M f ar b.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    exact ih.trans (gNet_rk_lt hs har e).le

theorem rk_top_lt {c : Fin m} {σ : Row m} (hc : isNT f c = true) (hs : Std S M f) (hσ : σ ∈ rowsOf S M f c) : rkN S M f ar (.top c) < rkN S M f ar (.part c σ) := by
  have h₁ := numAbove_lt (S := S) (M := M) (f := f) (u := .top c) (v := .part c σ) (exists_of_isNT hc) (by simp) (hs.top_up_part hc hσ)
  have h₂ : (numAbove S M f (.top c) + 1) * (m + 2) ≤ numAbove S M f (.part c σ) * (m + 2) := Nat.mul_le_mul_right _ h₁
  have h₃ : galPos S ar m (.top c) = 0 := rfl
  unfold rkN
  rw [h₃]
  nlinarith

/-- A path to a node of a gall stays on the gall, or comes through its coalescent node. -/
theorem gNet_path {c : Fin m} {l : List ({v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none})} {u : VNode S M f} : ∀ {v : VNode S M f}, (gNet hs har).IsPath u v l → InGall c v.1 →
    (InGall c u.1 ∧ ∀ e ∈ l, InGall c ((gNet hs har).tgt e).1) ∨ ∃ e ∈ l, ((gNet hs har).tgt e).1 = .top c := by
  induction l using List.reverseRecOn with
  | nil =>
    intro v h hv
    have huv : u = v := h
    exact Or.inl ⟨huv ▸ hv, by simp⟩
  | append_singleton l₀ e ih =>
    intro v h hv
    obtain ⟨y, h₁, h₂, h₃⟩ := Gusfield2007.Network.isPath_append.1 h
    have h₃' : (gNet hs har).tgt e = v := h₃
    have h₂' : (gNet hs har).src e = y := h₂
    by_cases het : ((gNet hs har).tgt e).1 = .top c
    · exact Or.inr ⟨e, by simp, het⟩
    · have hsrc := gNet_back hs har e (by rw [h₃']; exact hv) het
      rw [h₂'] at hsrc
      rcases ih h₁ hsrc with ⟨h₄, h₅⟩ | ⟨e', he', h₄⟩
      · refine Or.inl ⟨h₄, fun g hg => ?_⟩
        rcases List.mem_append.1 hg with hg | hg
        · exact h₅ g hg
        · rw [List.mem_singleton.1 hg, h₃']
          exact hv
      · exact Or.inr ⟨e', by simp [he'], h₄⟩

/-- **A recombination cycle of the network is on the gall of a component.** -/
theorem gNet_cycle {w x : VNode S M f} {p q : List ({v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none})} (hc : (gNet hs har).IsCycleOn w x p q) :
    ∃ c, isNT f c = true ∧ x.1 = .part c (ar c).1 ∧ ∀ v ∈ (gNet hs har).blobVerts {e | e ∈ p ∨ e ∈ q}, InGall c v.1 := by
  obtain ⟨c, hc₁, hx⟩ := gNet_isRecomb hs har hc.1
  refine ⟨c, hc₁, hx, ?_⟩
  have hxg : InGall c x.1 := Or.inr ⟨_, hx⟩
  have hxne : x.1 ≠ .top c := by
    rw [hx]
    simp
  have hrev : ∀ {P : List _}, (gNet hs har).IsPath w x P → ∀ {e}, e ∈ P → ((gNet hs har).tgt e).1 = .top c → InGall c w.1 → False := by
    intro P hP e he hte hw
    have h₁ : rkN S M f ar w.1 ≤ rkN S M f ar ((gNet hs har).src e).1 := gNet_rk_le hs har (hP.reach_src_of_mem he)
    have h₂ := gNet_rk_lt hs har e
    rw [hte] at h₂
    rcases hw with h₃ | ⟨σ, h₃⟩
    · rw [h₃] at h₁
      omega
    · have hσ : σ ∈ rowsOf S M f c := by
        have := w.2
        rw [h₃] at this
        exact this.2
      have := rk_top_lt (ar := ar) hc₁ hs hσ
      rw [h₃] at h₁
      omega
  have hP := gNet_path hs har (c := c) hc.2.1 hxg
  have hQ := gNet_path hs har (c := c) hc.2.2.1 hxg
  rcases hP with ⟨hw, hP⟩ | ⟨e, he, hte⟩ <;> rcases hQ with ⟨hw', hQ⟩ | ⟨g, hg, htg⟩
  · have hall : ∀ e, (e ∈ p ∨ e ∈ q) → InGall c ((gNet hs har).tgt e).1 := by
      rintro e (h | h)
      · exact hP e h
      · exact hQ e h
    have hsrc : ∀ e, (e ∈ p ∨ e ∈ q) → InGall c ((gNet hs har).src e).1 := by
      have hv : ∀ {P : List _}, (gNet hs har).IsPath w x P → (∀ e ∈ P, InGall c ((gNet hs har).tgt e).1) → ∀ e ∈ P, InGall c ((gNet hs har).src e).1 := by
        intro P hPp hPt e he
        have hm := hPp.src_mem_pathVerts he
        rcases List.mem_cons.1 hm with h | h
        · rw [h]
          exact hw
        · obtain ⟨g, hg, hge⟩ := List.mem_map.1 h
          rw [← hge]
          exact hPt g hg
      rintro e (h | h)
      · exact hv hc.2.1 hP e h
      · exact hv hc.2.2.1 hQ e h
    rintro v (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact hsrc e he
    · exact hall e he
  · exact (hrev hc.2.2.1 hg htg hw).elim
  · exact (hrev hc.2.1 he hte hw').elim
  · exfalso
    have heq : (gNet hs har).tgt e = (gNet hs har).tgt g := Subtype.ext (hte.trans htg.symm)
    have := hc.2.2.2.2 e he g hg heq
    apply hxne
    rw [← this, hte]

instance : Finite (GNode m) := by
  refine Finite.of_injective (β := Option (Fin m ⊕ (Fin m × Row m) ⊕ Row m)) (fun v => match v with
    | .root => none
    | .top c => some (.inl c)
    | .part c σ => some (.inr (.inl (c, σ)))
    | .leaf r => some (.inr (.inr r))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-- **The network is a galled tree.** -/
theorem gNet_isGalledTree : IsGalledTree (gNet hs har) := by
  rintro Q ⟨w, x, p, q, hc, rfl⟩
  refine ⟨⟨w, x, p, q, hc, rfl⟩, ?_⟩
  rintro Q' ⟨w', x', p', q', hc', rfl⟩ hne
  rw [Set.disjoint_left]
  intro v hv hv'
  obtain ⟨c, hc₁, hx, hall⟩ := gNet_cycle hs har hc
  obtain ⟨c', -, hx', hall'⟩ := gNet_cycle hs har hc'
  obtain rfl := (hall v hv).unique (hall' v hv')
  have hxx : x' = x := Subtype.ext (hx'.trans hx.symm)
  subst hxx
  apply hne
  refine (cycle_unique hc hc' fun y hy hyv hr => hy ?_).symm
  obtain ⟨c₂, -, hy₂⟩ := gNet_isRecomb hs har hr
  have hg := hall y hyv
  obtain rfl := hg.unique (Or.inr ⟨_, hy₂⟩)
  exact Subtype.ext (hy₂.trans hx.symm)

/-- **The network derives the rows.** -/
theorem gNet_derives : (gNet hs har).Derives M.toFinset := by
  have hleaf : ∀ {v : VNode S M f}, (gNet hs har).IsLeaf v → ∃ r ∈ M, v.1 = .leaf r := by
    intro v hv
    by_contra hno
    push Not at hno
    have hnl : ∀ ρ, v.1 ≠ .leaf ρ := by
      intro ρ h
      have hρ : ρ ∈ M := by
        have := v.2
        rw [h] at this
        exact this
      exact hno ρ hρ h
    obtain ⟨w, hw, hwp⟩ := exists_child hs har v.2 hnl
    obtain ⟨e, he, -⟩ := gNet_exists_arc hs har (v := ⟨w, hw⟩) hwp
    exact hv e (Subtype.ext he)
  have hlab : ∀ (r : Row m) (h : Valid S M f (.leaf r)), (gNet hs har).label ⟨.leaf r, h⟩ = r := fun _ h => funext fun i => label_leaf hs h i
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
  · obtain ⟨r, hr, h⟩ := hleaf hv
    have hve : v = ⟨.leaf r, hr⟩ := Subtype.ext h
    rw [hve, hlab r hr]
    exact Finset.mem_coe.2 (List.mem_toFinset.2 hr)
  · obtain ⟨r, hr, h⟩ := hleaf hu
    obtain ⟨r', hr', h'⟩ := hleaf hv
    have hue : u = ⟨.leaf r, hr⟩ := Subtype.ext h
    have hve : v = ⟨.leaf r', hr'⟩ := Subtype.ext h'
    rw [hue, hve, hlab r hr, hlab r' hr'] at huv
    rw [hue, hve]
    exact Subtype.ext (congrArg GNode.leaf huv)
  · have hrM : r ∈ M := List.mem_toFinset.1 hr
    refine ⟨⟨.leaf r, hrM⟩, fun e he => ?_, hlab r hrM⟩
    have harc := gNet_arc hs har e
    exact par_not_leaf hs ((gNet hs har).tgt e).2 harc r (by rw [he])

include hs in
/-- A component with conflicts has an edge at each site. -/
theorem Std.exists_adj_of_isNT {c : Fin m} (hc : isNT f c = true) {i : Fin m} (hi : f i = c) : ∃ k, f k = c ∧ (incompatGraph (addRow M.toFinset S)).Adj i k := by
  have hlen : 1 < (sitesOf f c).length := by simpa [isNT] using hc
  have hnd : (sitesOf f c).Nodup := (List.nodup_finRange m).filter _
  rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff] at hlen
  obtain ⟨a, b, ha, hb, hab⟩ := hlen
  have hfa : f a = c := by simpa [sitesOf] using ha
  have hfb : f b = c := by simpa [sitesOf] using hb
  obtain ⟨j, hj, hji⟩ : ∃ j, f j = c ∧ j ≠ i := by
    by_cases h : a = i
    · exact ⟨b, hfb, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨a, hfa, h⟩
  obtain ⟨k, hk⟩ := exists_adj_of_reachable ((hs.lab i j).1 (hi.trans hj.symm)) (Ne.symm hji)
  exact ⟨k, ((hs.lab i k).2 (SimpleGraph.Adj.reachable hk)).symm.trans hi, hk⟩

/-- The node below the arc of a site, in the network. -/
theorem gNet_tgt_site (i : Fin m) : ((gNet hs har).tgt ((gNet hs har).site i)).1 = siteNode S f ar i := by
  have h : (gPreNet hs har).site i = some (Exists.choose (⟨_, rfl⟩ : ∃ v, (gPreNet hs har).site i = some v)) := Exists.choose_spec (⟨_, rfl⟩ : ∃ v, (gPreNet hs har).site i = some v)
  exact (congrArg Subtype.val (Option.some.inj h)).symm

/-- The rows of `M + S` label nodes of the network. -/
theorem gNet_labels : ∀ r ∈ addRow M.toFinset S, ∃ v, (gNet hs har).label v = r := by
  intro r hr
  rcases mem_addRow.1 hr with rfl | hr
  · exact ⟨⟨.root, trivial⟩, funext label_root⟩
  · have hrM : r ∈ M := List.mem_toFinset.1 hr
    exact ⟨⟨.leaf r, hrM⟩, funext fun i => label_leaf hs hrM i⟩

/-- **The network is a reduced galled tree** (Definition 2.2 of the source). -/
theorem gNet_reduced : IsReducedGalledTree (gNet hs har) (conflictGraph S M.toFinset) := by
  rw [conflictGraph_eq_incompatGraph_addRow]
  have hG := gNet_isGalledTree hs har
  have hsiteOf : ∀ {c : Fin m} {i : Fin m}, isNT f c = true → f i = c → InGall c ((gNet hs har).tgt ((gNet hs har).site i)).1 := by
    intro c i hc hi
    subst hi
    obtain ⟨z, h, -⟩ := siteNode_spec (ar := ar) har hc
    rw [gNet_tgt_site, h]
    exact Or.inr ⟨z, rfl⟩
  refine ⟨hG, fun Q hQ => ?_, fun Q hQ i hi => ?_⟩
  · obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ
    obtain ⟨c, hc₁, hx, hall⟩ := gNet_cycle hs har hc
    obtain ⟨a, ha⟩ := exists_of_isNT (f := f) hc₁
    obtain ⟨k, hk, hadj⟩ := hs.exists_adj_of_isNT hc₁ ha
    obtain ⟨Q₀, ⟨w₀, x₀, p₀, q₀, hc₀, rfl⟩, hsa, hsk⟩ := exists_isCycle_of_incompatible (gNet hs har) (gNet_labels hs har) hadj
    obtain ⟨c₀, -, hx₀, hall₀⟩ := gNet_cycle hs har hc₀
    have hin₀ := hall₀ _ (Or.inr ⟨_, hsa, rfl⟩)
    obtain rfl := hin₀.unique (hsiteOf hc₁ ha)
    have hxx : x₀ = x := Subtype.ext (hx₀.trans hx.symm)
    subst hxx
    have heq : {e | e ∈ p ∨ e ∈ q} = {e | e ∈ p₀ ∨ e ∈ q₀} := cycle_unique hc hc₀ fun y hy hyv hr => hy (by
      obtain ⟨c₂, -, hy₂⟩ := gNet_isRecomb hs har hr
      obtain rfl := (hall y hyv).unique (Or.inr ⟨_, hy₂⟩)
      exact Subtype.ext (hy₂.trans hx.symm))
    exact ⟨a, k, heq ▸ hsa, heq ▸ hsk, hadj⟩
  · obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ
    obtain ⟨c, hc₁, -, hall⟩ := gNet_cycle hs har hc
    have hin := hall _ (Or.inr ⟨_, hi, rfl⟩)
    by_cases hci : isNT f (f i) = true
    · obtain rfl := hin.unique (hsiteOf hci rfl)
      obtain ⟨k, -, hk⟩ := hs.exists_adj_of_isNT hci rfl
      exact ⟨k, hk⟩
    · rw [gNet_tgt_site] at hin
      have hsn : siteNode S f ar i = .top (f i) := by simp [siteNode, hci]
      rw [hsn] at hin
      obtain rfl : f i = c := by
        rcases hin with h | ⟨σ, h⟩
        · exact GNode.top.inj h
        · simp at h
      exact absurd hc₁ hci

end Assemble

/-! ### The arrangement from the test -/

theorem mem_sitesOf {c i : Fin m} : i ∈ sitesOf f c ↔ f i = c := by
  simp [sitesOf]

theorem off_rowsOf {c : Fin m} {σ : Row m} (hσ : σ ∈ rowsOf S M f c) {i : Fin m} (hi : f i ≠ c) : σ i = S i := by
  obtain ⟨⟨r, -, rfl⟩, -⟩ := mem_rowsOf.1 hσ
  simp [mkRow, hi]

theorem arrOf_ok {c : Fin m} (hex : ∃ s ∈ rowsOf S M f c, (candidate S (sitesOf f c) (rowsOf S M f c) s).1 = true) : ArrOK S M f c (arrOf S M f c) := by
  obtain ⟨s₀, hs₀, hs₀c⟩ := hex
  have hnone : (rowsOf S M f c).find? (fun s => (candidate S (sitesOf f c) (rowsOf S M f c) s).1) ≠ none := by
    intro h
    have := List.find?_eq_none.1 h s₀ hs₀
    rw [hs₀c] at this
    exact absurd this (by simp)
  obtain ⟨s, hfind⟩ := Option.ne_none_iff_exists'.1 hnone
  have hsc' := List.find?_some hfind
  have hsc : (candidate S (sitesOf f c) (rowsOf S M f c) s).1 = true := hsc'
  have hs : s ∈ rowsOf S M f c := List.mem_of_find?_eq_some hfind
  unfold arrOf
  rw [hfind]
  dsimp only
  have hcand := hsc
  unfold candidate at hcand
  dsimp only at hcand
  have heqOn : ∀ {a b : Row m}, a ∈ rowsOf S M f c → b ∈ rowsOf S M f c → (∀ i ∈ sitesOf f c, a i = b i) → a = b := by
    intro a b ha hb h
    funext i
    by_cases hi : f i = c
    · exact h i (mem_sitesOf.2 hi)
    · rw [off_rowsOf ha hi, off_rowsOf hb hi]
  have hrest : ∀ {r}, r ∈ (filterOps (rowsOf S M f c) fun r => (!(eqOn (sitesOf f c) r s).1, (eqOn (sitesOf f c) r s).2)).1 ↔ r ∈ rowsOf S M f c ∧ r ≠ s := by
    intro r
    constructor
    · intro hr
      obtain ⟨h₁, h₂⟩ := List.mem_filter.1 hr
      refine ⟨h₁, fun h₃ => ?_⟩
      have : (eqOn (sitesOf f c) r s).1 = true := eqOn_iff.2 fun i _ => by rw [h₃]
      simp [this] at h₂
    · rintro ⟨h₁, h₂⟩
      refine List.mem_filter.2 ⟨h₁, ?_⟩
      have : ¬ (eqOn (sitesOf f c) r s).1 = true := fun h' => h₂ (heqOn h₁ hs (eqOn_iff.1 h'))
      simpa using this
  split
  · rename_i hnil
    rw [hnil] at hcand
    simp at hcand
  · rename_i seed tl hRR
    rw [hRR] at hcand hrest
    have hrestM : ∀ {r}, r ∈ seed :: tl → r ∈ rowsOf S M f c ∧ r ≠ s := hrest.1
    dsimp only at hcand
    generalize hA : (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1 = A at hcand ⊢
    generalize hB : (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1 = B at hcand ⊢
    have hAm : ∀ {y}, y ∈ A → y ∈ rowsOf S M f c ∧ y ≠ s := fun {y} hy => hrestM (by
      rw [← hA] at hy
      exact (List.mem_filter.1 hy).1)
    have hBm : ∀ {y}, y ∈ B → y ∈ rowsOf S M f c ∧ y ≠ s := fun {y} hy => hrestM (by
      rw [← hB] at hy
      exact (List.mem_filter.1 hy).1)
    have hsplit : ∀ {σ}, σ ∈ rowsOf S M f c → σ = s ∨ σ ∈ A ∨ σ ∈ B := by
      intro σ hσ
      by_cases hσs : σ = s
      · exact Or.inl hσs
      have hσr : σ ∈ seed :: tl := hrest.2 ⟨hσ, hσs⟩
      by_cases hcmp : (cmpOn S (sitesOf f c) seed σ).1 = true
      · exact Or.inr (Or.inl (by rw [← hA]; exact List.mem_filter.2 ⟨hσr, hcmp⟩))
      · exact Or.inr (Or.inr (by rw [← hB]; exact List.mem_filter.2 ⟨hσr, by simpa using hcmp⟩))
    have hsub : ∀ {a b : Row m}, a ∈ rowsOf S M f c → (∀ i ∈ sitesOf f c, a i ≠ S i → b i ≠ S i) → Sub1 S a b := by
      intro a b ha h i hi
      by_cases hic : f i = c
      · exact h i (mem_sitesOf.2 hic) hi
      · exact absurd (off_rowsOf ha hic) hi
    have hch : ∀ {X : List (Row m)}, (∀ {y}, y ∈ X → y ∈ rowsOf S M f c ∧ y ≠ s) → (∀ a ∈ X, ∀ b ∈ X, (cmpOn S (sitesOf f c) a b).1 = true) → Ch S X := by
      intro X hX h a ha b hb
      rcases cmpOn_iff.1 (h a ha b hb) with h' | h'
      · exact Or.inl (hsub (hX ha).1 h')
      · exact Or.inr (hsub (hX hb).1 h')
    simp only [Bool.and_eq_true, allOps, anyOps, List.all_eq_true, List.any_eq_true, Bool.or_eq_true] at hcand
    obtain ⟨⟨⟨⟨hchA, hchB⟩, hdj⟩, hcov⟩, n, hn, hrc⟩ := hcand
    have hdisj : ∀ x ∈ A, ∀ y ∈ B, ∀ i, x i ≠ S i → y i = S i := by
      intro x hx y hy i hi
      by_cases hic : f i = c
      · exact disjOn_iff.1 (hdj x hx y hy) i (mem_sitesOf.2 hic) hi
      · exact off_rowsOf (hBm hy).1 hic
    have hdisj' : ∀ x ∈ B, ∀ y ∈ A, ∀ i, x i ≠ S i → y i = S i := by
      intro x hx y hy i hi
      by_contra hne
      exact hi (hdisj y hy x hx i hne)
    have hcover : ∀ i, f i = c → (∃ y ∈ A, y i ≠ S i) ∨ ∃ y ∈ B, y i ≠ S i := by
      intro i hi
      rcases hcov i (mem_sitesOf.2 hi) with ⟨y, hy, hyi⟩ | ⟨y, hy, hyi⟩
      · exact Or.inl ⟨y, hy, by simpa [flipAt] using hyi⟩
      · exact Or.inr ⟨y, hy, by simpa [flipAt] using hyi⟩
    have hpt : ∀ {X Y : List (Row m)} {n' : ℕ}, (recombOk S (sitesOf f c) X Y s n').1 = true → ∃ n, ∀ i, f i = c → s i = if i.val < n then topAt S Y i else topAt S X i := by
      intro X Y n' h
      simp only [recombOk, allOps, List.all_eq_true, beq_iff_eq] at h
      exact ⟨n', fun i hi => h i (mem_sitesOf.2 hi)⟩
    split_ifs with hany
    · obtain ⟨n', -, hn'⟩ := List.any_eq_true.1 hany
      exact ⟨hs, fun y hy => hAm hy, fun y hy => hBm hy, fun σ hσ => hsplit hσ, hch hAm hchA, hch hBm hchB, hdisj, hcover, hpt hn'⟩
    · rcases hrc with h | h
      · exact absurd (List.any_eq_true.2 ⟨n, hn, h⟩) hany
      · exact ⟨hs, fun y hy => hBm hy, fun y hy => hAm hy, fun σ hσ => (hsplit hσ).imp_right Or.symm, hch hBm hchB, hch hAm hchA, hdisj', fun i hi => (hcover i hi).symm, hpt h⟩

end Laminar

/-! ### The function -/

/-- The table of the network: for each node, its parents and its label. -/
def gTable (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m) : List (GNode m × Option (GNode m) × Option (GNode m) × List Bool) :=
  (cands S M f ++ M.map GNode.leaf).map fun v => (v, par S M f ar v, par₂ S ar v, List.ofFn (label S M f v))

/-- What the algorithm returns: the table of the nodes, and the node below the arc of each site. -/
abbrev GalledOut (m : ℕ) := List (GNode m × Option (GNode m) × Option (GNode m) × List Bool) × List (GNode m)

/-- **The algorithm** (`ext:galled_build`), Sections 3 to 7 of the source: decide, and when there is a galled tree, return a reduced one as a table. -/
def galledBuild (S : Row m) (M : List (Row m)) : Option (GalledOut m) :=
  if (galledDecide S M).1 then
    let f := labOf (edgesOps S M).1
    let t := List.ofFn (arrOf S M f)
    let ar : Fin m → Arr m := fun c => t.getD c.val (S, [], [])
    some (gTable S M f ar, List.ofFn (siteNode S f ar))
  else none

section Correct

open scoped Classical

open Gusfield2007 Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

theorem mem_nodes {f : Fin m → Fin m} {v : GNode m} : v ∈ cands S M f ++ M.map GNode.leaf ↔ Valid S M f v := by
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact valid_of_mem_cands h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
      exact hr
  · intro h
    by_cases hl : ∀ ρ, v ≠ .leaf ρ
    · exact List.mem_append_left _ (mem_cands_of_valid h hl)
    · push Not at hl
      obtain ⟨ρ, rfl⟩ := hl
      exact List.mem_append_right _ (List.mem_map.2 ⟨ρ, h, rfl⟩)

theorem std_of (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) : Std S M (labOf (edgesOps S M).1) := ⟨lab_iff, hM, h1⟩

/-- A galled tree gives the arrangements (Theorem 3.2 of the source). -/
theorem arrOf_ok_of_galled (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) {V E : Type*} [Finite V] {N : Network (Fin m) V E} (hG : IsGalledTree N) (hc₁ : N.Obeys .single) (hD : N.Derives M.toFinset) (hS : N.ancestral = S) {c : Fin m}
    (hc : isNT (labOf (edgesOps S M).1) c = true) : ArrOK S M (labOf (edgesOps S M).1) c (arrOf S M (labOf (edgesOps S M).1) c) := by
  subst hS
  obtain ⟨k₀, rfl⟩ := exists_of_isNT hc
  refine arrOf_ok ?_
  have hnt := (one_lt_length_iff (S := N.ancestral) (M := M) k₀).1 (of_decide_eq_true hc)
  have hCl : ∀ i, i ∈ sitesOf (labOf (edgesOps N.ancestral M).1) (labOf (edgesOps N.ancestral M).1 k₀) ↔ i ∈ ((incompatGraph (addRow M.toFinset N.ancestral)).connectedComponentMk k₀).supp := mem_filter_lab k₀
  refine exists_candidate_of_gall hG hc₁ hD _ hnt hCl (fun r hr => ?_) (fun r hr h => ?_) (fun ρ hρ hne => ?_)
  · obtain ⟨⟨ρ, hρ, rfl⟩, -⟩ := mem_rowsOf.1 hr
    exact ⟨ρ, hρ, fun i hi => by simp [mkRow, mem_sitesOf.1 hi]⟩
  · obtain ⟨⟨ρ, hρ, rfl⟩, hne⟩ := mem_rowsOf.1 hr
    apply hne
    funext i
    by_cases hi : labOf (edgesOps N.ancestral M).1 i = labOf (edgesOps N.ancestral M).1 k₀
    · exact h i (mem_sitesOf.2 hi)
    · simp [mkRow, hi]
  · refine ⟨mkRow N.ancestral (labOf (edgesOps N.ancestral M).1) (labOf (edgesOps N.ancestral M).1 k₀) ρ, mem_rowsOf.2 ⟨⟨ρ, hρ, rfl⟩, fun h => hne fun i hi => ?_⟩, fun i hi => by simp [mkRow, mem_sitesOf.1 hi]⟩
    have := congrFun h i
    simpa [mkRow, mem_sitesOf.1 hi] using this

/-- **The algorithm returns something exactly when there is a galled tree** (`ext:galled_build`), for the rows `M` and the ancestral sequence `S`, with the source's standing assumptions that there are rows and each column has a `1`. -/
theorem galledBuild_isSome_iff (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) :
    (galledBuild S M).isSome = true ↔ ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), IsGalledTree N ∧ N.Obeys .single ∧ N.Derives M.toFinset ∧ N.ancestral = S := by
  rw [← galledDecide_iff hM h1]
  unfold galledBuild
  by_cases h : (galledDecide S M).1 = true <;> simp [h]

/-- **What the algorithm returns is a reduced galled tree** (`ext:galled_build`), Gusfield et al. 2007, line 180. If `galledBuild` returns a table, it is the table of the network `gNet`: its nodes are those of the table (`mem_nodes`), its arcs go from the parents of the table (`gNet_arc`, `gNet_exists_arc`), its labels are those of the table (`gNet_label`), and the sites are on the arcs into the nodes the second list gives (`gNet_tgt_site`). That network is a reduced galled tree for `M`, with ancestral sequence `S` and single crossovers. -/
theorem galledBuild_correct (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) {t : GalledOut m} (ht : galledBuild S M = some t) :
    ∃ (f : Fin m → Fin m) (ar : Fin m → Arr m) (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c)), t = (gTable S M f ar, List.ofFn (siteNode S f ar)) ∧
      (gNet hs har).Obeys .single ∧ (gNet hs har).Derives M.toFinset ∧ (gNet hs har).ancestral = S ∧ IsReducedGalledTree (gNet hs har) (conflictGraph S M.toFinset) := by
  unfold galledBuild at ht
  split_ifs at ht with hdec
  have hs := std_of hM h1
  obtain ⟨a, b, N, hG, hc₁, hD, hSN⟩ := (galledDecide_iff hM h1).1 hdec
  have har₀ : ∀ c, isNT (labOf (edgesOps S M).1) c = true → ArrOK S M (labOf (edgesOps S M).1) c (arrOf S M (labOf (edgesOps S M).1) c) := fun c hc => arrOf_ok_of_galled h1 hG hc₁ hD hSN hc
  have har : (fun c : Fin m => (List.ofFn (arrOf S M (labOf (edgesOps S M).1))).getD c.val (S, [], [])) = arrOf S M (labOf (edgesOps S M).1) := by
    funext c
    simp [List.getD_eq_getElem?_getD]
  simp only [har] at ht
  exact ⟨_, _, hs, har₀, (Option.some.inj ht).symm, gNet_obeys hs har₀, gNet_derives hs har₀, gNet_ancestral hs har₀, gNet_reduced hs har₀⟩

end Correct

end GusfieldEtAl2004.Algorithm
