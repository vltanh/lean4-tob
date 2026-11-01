module

public import Gusfield2007.Defs
public import Gusfield2007.TimeOrdered
public import Gusfield2007.NetworkOps
public import Mathlib.Data.EReal.Basic

/-!
# The bound of Song and Hein by ordered-SPR operations

See the `README.md` of this directory. The source has no proof, only the construction in words: "a subtree that gets pruned and regrafted in an SPR operation corresponds to the descendant subtree of a recombination vertex in an ARG". This is that construction of an ancestral recombination graph from a sequence of trees: going along the sites, each
ordered-SPR operation is one recombination node, just above the root of the pruned subtree.

The network is built with the sites placed one by one, and it's kept in a state where the arcs followed to the right of the last crossover form the current tree. The state is described by times: a node `n` at
time `t n` on the path up from the row `r` has below it exactly the rows of the edge of the current tree above `r` at that time (`lin`, `Realizes.J`).
-/

@[expose] public noncomputable section

open scoped Classical

namespace SongHein2005

open Gusfield2007

section Lin

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The time of a cluster, `⊤` at a leaf. -/
def tm (T : TimeOrderedTree X) (D : Finset X) : EReal := if 2 ≤ D.card then (T.time D : EReal) else ⊤

variable {T : TimeOrderedTree X}

theorem tm_of_two_le {D : Finset X} (h : 2 ≤ D.card) : tm T D = (T.time D : EReal) := ite_eq_left h

theorem tm_ne_bot (D : Finset X) : tm T D ≠ ⊥ := by
  unfold tm
  split_ifs
  · exact EReal.coe_ne_bot _
  · exact top_ne_bot

theorem comparable_of_mem {A B : Finset X} (hA : A ∈ T.clusters) (hB : B ∈ T.clusters) {r : X} (hrA : r ∈ A) (hrB : r ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases T.isHierarchy.2.2.2 A hA B hB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hrB (Finset.disjoint_left.1 h hrA)

theorem two_le_card_of_ssubset {A B : Finset X} (hA : A ∈ T.clusters) (h : A ⊂ B) : 2 ≤ B.card := by
  have h₁ := Finset.card_lt_card h
  have h₂ := Finset.card_pos.2 (T.isHierarchy.2.2.1 A hA)
  omega

theorem tm_lt_of_ssubset {A B : Finset X} (hA : A ∈ T.clusters) (hB : B ∈ T.clusters) (h : A ⊂ B) : tm T B < tm T A := by
  rw [tm_of_two_le (two_le_card_of_ssubset hA h)]
  unfold tm
  split_ifs with hc
  · exact EReal.coe_lt_coe_iff.2 (T.time_lt A hA B hB hc h)
  · exact EReal.coe_lt_top _

theorem tm_le_of_subset {A B : Finset X} (hA : A ∈ T.clusters) (hB : B ∈ T.clusters) (h : A ⊆ B) : tm T B ≤ tm T A := by
  rcases h.eq_or_ssubset with rfl | h
  · exact le_rfl
  · exact (tm_lt_of_ssubset hA hB h).le

variable (T)

/-- `D` is the edge of `T` above the row `r` at the time `τ`, named by the cluster below it: the largest cluster with `r` not earlier than `τ`. -/
structure IsLin (r : X) (τ : EReal) (D : Finset X) : Prop where
  mem : D ∈ T.clusters
  mem_row : r ∈ D
  le_tm : τ ≤ tm T D
  max : ∀ D' ∈ T.clusters, r ∈ D' → τ ≤ tm T D' → D' ⊆ D

theorem exists_isLin (r : X) (τ : EReal) : ∃ D, IsLin T r τ D := by
  have hne : (T.clusters.filter fun D => r ∈ D ∧ τ ≤ tm T D).Nonempty :=
    ⟨{r}, Finset.mem_filter.2 ⟨T.isHierarchy.2.1 r, Finset.mem_singleton_self r, by simp [tm]⟩⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  obtain ⟨hD₁, hD₂, hD₃⟩ := Finset.mem_filter.1 hD
  refine ⟨D, hD₁, hD₂, hD₃, fun D' hD' hr hτ => ?_⟩
  rcases comparable_of_mem hD' hD₁ hr hD₂ with h | h
  · exact h
  · have := hmax D' (Finset.mem_filter.2 ⟨hD', hr, hτ⟩)
    exact (Finset.eq_of_subset_of_card_le h this).symm.subset

/-- The edge of `T` above the row `r` at the time `τ`. -/
def lin (r : X) (τ : EReal) : Finset X := (exists_isLin T r τ).choose

theorem isLin_lin (r : X) (τ : EReal) : IsLin T r τ (lin T r τ) := (exists_isLin T r τ).choose_spec

variable {T}

theorem IsLin.lin_eq {r : X} {τ : EReal} {D : Finset X} (h : IsLin T r τ D) : lin T r τ = D :=
  (h.max _ (isLin_lin T r τ).mem (isLin_lin T r τ).mem_row (isLin_lin T r τ).le_tm).antisymm
    ((isLin_lin T r τ).max _ h.mem h.mem_row h.le_tm)

theorem lin_eq_of_mem {r r' : X} {τ : EReal} (h : r' ∈ lin T r τ) : lin T r' τ = lin T r τ := by
  have hl := isLin_lin T r τ
  refine IsLin.lin_eq ⟨hl.mem, h, hl.le_tm, fun D' hD' hr' hτ => ?_⟩
  rcases comparable_of_mem hD' hl.mem hr' h with h₁ | h₁
  · exact h₁
  · exact hl.max D' hD' (h₁ hl.mem_row) hτ

theorem lin_tm {D : Finset X} (hD : D ∈ T.clusters) {r : X} (hr : r ∈ D) : lin T r (tm T D) = D := by
  refine IsLin.lin_eq ⟨hD, hr, le_rfl, fun D' hD' hr' hτ => ?_⟩
  rcases comparable_of_mem hD' hD hr' hr with h | h
  · exact h
  · rcases h.eq_or_ssubset with rfl | h
    · exact subset_rfl
    · exact absurd hτ (not_le.2 (tm_lt_of_ssubset hD hD' h))

theorem lin_bot (r : X) : lin T r ⊥ = Finset.univ :=
  IsLin.lin_eq ⟨T.isHierarchy.1, Finset.mem_univ r, bot_le, fun _ _ _ _ => Finset.subset_univ _⟩

/-- A row of a cluster not earlier than `τ` is in the same edge at `τ`. -/
theorem subset_lin {D : Finset X} (hD : D ∈ T.clusters) {r : X} (hr : r ∈ D) {τ : EReal} (hτ : τ ≤ tm T D) : D ⊆ lin T r τ :=
  (isLin_lin T r τ).max D hD hr hτ

/-- The smallest cluster strictly above `A`. -/
theorem exists_parent {A : Finset X} (hne : A ≠ Finset.univ) :
    ∃ P ∈ T.clusters, A ⊂ P ∧ ∀ E ∈ T.clusters, A ⊂ E → A.Nonempty → P ⊆ E := by
  have hs : A ⊂ Finset.univ := (Finset.subset_univ A).ssubset_of_ne hne
  have hnon : (T.clusters.filter fun E => A ⊂ E).Nonempty := ⟨_, Finset.mem_filter.2 ⟨T.isHierarchy.1, hs⟩⟩
  obtain ⟨P, hP, hmin⟩ := Finset.exists_min_image _ Finset.card hnon
  obtain ⟨hP₁, hP₂⟩ := Finset.mem_filter.1 hP
  refine ⟨P, hP₁, hP₂, fun E hE hAE hAne => ?_⟩
  obtain ⟨r, hr⟩ := hAne
  rcases comparable_of_mem hP₁ hE (hP₂.subset hr) (hAE.subset hr) with h | h
  · exact h
  · exact Finset.eq_of_subset_of_card_le h (hmin E (Finset.mem_filter.2 ⟨hE, hAE⟩)) ▸ subset_rfl

end Lin

section SPR

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- An ordered-SPR operation on the cluster `A`: the conjuncts of `TimeOrderedTree.IsOrderedSPR`. -/
structure SPRAt (T T' : TimeOrderedTree X) (A : Finset X) : Prop where
  mem : A ∈ T.clusters
  mem' : A ∈ T'.clusters
  ne_univ : A ≠ Finset.univ
  sub : ∀ B ⊆ A, B ∈ T.clusters ↔ B ∈ T'.clusters
  time : ∀ B ⊆ A, B ∈ T.clusters → 2 ≤ B.card → T.time B = T'.time B
  pr : T.prunedClusters A = T'.prunedClusters A
  prt : ∀ D ∈ T.prunedClusters A, 2 ≤ D.card → T.prunedTime A D = T'.prunedTime A D

variable {T T' : TimeOrderedTree X} {A : Finset X}

/-- An ordered-SPR operation can be undone by one. -/
theorem SPRAt.symm (h : SPRAt T T' A) : SPRAt T' T A where
  mem := h.mem'
  mem' := h.mem
  ne_univ := h.ne_univ
  sub B hB := (h.sub B hB).symm
  time B hB hB' hc := (h.time B hB ((h.sub B hB).2 hB') hc).symm
  pr := h.pr.symm
  prt D hD hc := (h.prt D (h.pr ▸ hD) hc).symm

theorem SPRAt.tm_eq (h : SPRAt T T' A) {B : Finset X} (hB : B ⊆ A) (hB' : B ∈ T.clusters) : tm T B = tm T' B := by
  unfold tm
  split_ifs with hc
  · rw [h.time B hB hB' hc]
  · rfl

/-- What a pruned cluster is. -/
theorem mem_prunedClusters {G : Finset X} (hA : A ∈ T.clusters) (hG : G ∈ T.prunedClusters A) :
    (G ∈ T.clusters ∨ G ∪ A ∈ T.clusters) ∧ Disjoint G A ∧ G.Nonempty := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hG
  obtain ⟨hB₁, hB₂⟩ := Finset.mem_filter.1 hB
  have hne : (B \ A).Nonempty := Finset.sdiff_nonempty.2 hB₂
  refine ⟨?_, Finset.sdiff_disjoint, hne⟩
  rcases T.isHierarchy.2.2.2 B hB₁ A hA with h | h | h
  · exact absurd h hB₂
  · right
    rwa [Finset.sdiff_union_of_subset h]
  · left
    rwa [h.sdiff_eq_left]

/-- The retained cluster of a pruned cluster: the node of `T` that stays. -/
def retained (T : TimeOrderedTree X) (A G : Finset X) : Finset X := if G ∈ T.clusters then G else G ∪ A

theorem retained_mem (hA : A ∈ T.clusters) {G : Finset X} (hG : G ∈ T.prunedClusters A) : retained T A G ∈ T.clusters := by
  unfold retained
  split_ifs with h
  · exact h
  · exact (mem_prunedClusters hA hG).1.resolve_left h

theorem subset_retained (G : Finset X) : G ⊆ retained T A G := by
  unfold retained
  split_ifs
  · exact subset_rfl
  · exact Finset.subset_union_left

theorem tm_retained {G : Finset X} (hc : 2 ≤ G.card) : tm T (retained T A G) = (T.prunedTime A G : EReal) := by
  have hc' : 2 ≤ (retained T A G).card := hc.trans (Finset.card_le_card (subset_retained G))
  rw [tm_of_two_le hc']
  unfold retained TimeOrderedTree.prunedTime
  split_ifs <;> rfl

/-- The rows outside `A` see the same edges in the two trees, up to `A`: the first half. -/
theorem SPRAt.lin_sdiff_subset (h : SPRAt T T' A) {r : X} (hr : r ∉ A) (τ : EReal) : lin T r τ \ A ⊆ lin T' r τ := by
  set D := lin T r τ with hD
  have hl := isLin_lin T r τ
  have hDA : ¬ D ⊆ A := fun hs => hr (hs hl.mem_row)
  set G := D \ A with hGdef
  have hrG : r ∈ G := Finset.mem_sdiff.2 ⟨hl.mem_row, hr⟩
  have hGT : G ∈ T.prunedClusters A := Finset.mem_image.2 ⟨D, Finset.mem_filter.2 ⟨hl.mem, hDA⟩, rfl⟩
  have hGT' : G ∈ T'.prunedClusters A := h.pr ▸ hGT
  have hE : retained T' A G ∈ T'.clusters := retained_mem h.mem' hGT'
  refine (subset_retained G).trans (subset_lin hE (subset_retained G hrG) ?_)
  by_cases hc : 2 ≤ G.card
  · rw [tm_retained hc, ← h.prt G hGT hc, ← tm_retained hc]
    refine hl.le_tm.trans ?_
    have hDG : D = G ∨ D = G ∪ A := by
      rcases T.isHierarchy.2.2.2 D hl.mem A h.mem with h' | h' | h'
      · exact absurd h' hDA
      · right
        rw [hGdef, Finset.sdiff_union_of_subset h']
      · left
        rw [hGdef, h'.sdiff_eq_left]
    unfold retained
    split_ifs with hGmem
    · exact tm_le_of_subset hGmem hl.mem Finset.sdiff_subset
    · rcases hDG with h' | h'
      · exact absurd (h' ▸ hl.mem) hGmem
      · rw [← h']
  · have hG1 : G = {r} := by
      have hpos := Finset.card_pos.2 ⟨r, hrG⟩
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨hrG, fun x hx => Finset.card_le_one.1 (by omega) x hx r hrG⟩
    have hsing : G ∈ T'.clusters := hG1 ▸ T'.isHierarchy.2.1 r
    unfold retained
    rw [ite_eq_left hsing]
    simp [tm, hc]

/-- The rows outside `A` see the same edges in the two trees, up to `A`. -/
theorem SPRAt.mem_lin_iff (h : SPRAt T T' A) {r r' : X} (hr : r ∉ A) (hr' : r' ∉ A) (τ : EReal) : r' ∈ lin T r τ ↔ r' ∈ lin T' r τ :=
  ⟨fun h₁ => h.lin_sdiff_subset hr τ (Finset.mem_sdiff.2 ⟨h₁, hr'⟩), fun h₁ => h.symm.lin_sdiff_subset hr τ (Finset.mem_sdiff.2 ⟨h₁, hr'⟩)⟩

/-- The rows of `A`, below the edges above `A`, see the same edges in the two trees. -/
theorem SPRAt.lin_eq_of_mem (h : SPRAt T T' A) {r : X} (hr : r ∈ A) {τ : EReal} (h₁ : ∀ E ∈ T.clusters, A ⊂ E → tm T E < τ)
    (h₂ : ∀ E ∈ T'.clusters, A ⊂ E → tm T' E < τ) : lin T r τ = lin T' r τ := by
  have key : ∀ {T₁ : TimeOrderedTree X} {D : Finset X}, A ∈ T₁.clusters → (∀ E ∈ T₁.clusters, A ⊂ E → tm T₁ E < τ) → D ∈ T₁.clusters → r ∈ D → τ ≤ tm T₁ D → D ⊆ A := by
    intro T₁ D hA hE hD hrD hτ
    rcases comparable_of_mem hD hA hrD hr with h' | h'
    · exact h'
    · rcases h'.eq_or_ssubset with h'' | h''
      · exact h''.ge
      · exact absurd hτ (not_le.2 (hE D hD h''))
  refine (IsLin.lin_eq ?_).symm
  have hl := isLin_lin T r τ
  have hs := key h.mem h₁ hl.mem hl.mem_row hl.le_tm
  refine ⟨(h.sub _ hs).1 hl.mem, hl.mem_row, (h.tm_eq hs hl.mem) ▸ hl.le_tm, fun D' hD' hr' hτ => ?_⟩
  have hs' := key h.mem' h₂ hD' hr' hτ
  have hD'T := (h.sub _ hs').2 hD'
  exact hl.max D' hD'T hr' ((h.tm_eq hs' hD'T) ▸ hτ)

end SPR

section Chain

variable {ι : Type*} {V : Type*}

/-- `b` is at or above `a`, following the parent `par`, the one to the right of every crossover so far. -/
def Anc (P : PreNet ι V) (b a : V) : Prop := Relation.ReflTransGen (fun c p => P.par c = some p) a b

variable {P : PreNet ι V}

theorem Anc.refl (a : V) : Anc P a a := Relation.ReflTransGen.refl

theorem Anc.trans {a b c : V} (h₁ : Anc P c b) (h₂ : Anc P b a) : Anc P c a := Relation.ReflTransGen.trans h₂ h₁

theorem Anc.of_par {a b : V} (h : P.par a = some b) : Anc P b a := Relation.ReflTransGen.single h

theorem Anc.head {a b c : V} (h : P.par a = some c) (h₂ : Anc P b c) : Anc P b a := Relation.ReflTransGen.head h h₂

theorem Anc.eq_or_par {a b : V} (h : Anc P b a) : a = b ∨ ∃ p, P.par a = some p ∧ Anc P b p := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨p, hp, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hp, h⟩

/-- The nodes above a node are in a chain. -/
theorem Anc.total {a b c : V} (h₁ : Anc P a c) (h₂ : Anc P b c) : Anc P a b ∨ Anc P b a := by
  induction h₁ with
  | refl => exact Or.inr h₂
  | @tail a' a _ hstep ih =>
    rcases ih with ih | ih
    · exact Or.inl (Anc.trans (Anc.of_par hstep) ih)
    · rcases ih.eq_or_par with rfl | ⟨p, hp, hr⟩
      · exact Or.inl (Anc.of_par hstep)
      · obtain rfl : p = a := Option.some_inj.1 (hp.symm.trans hstep)
        exact Or.inr hr

theorem not_anc_of_par {a b : V} (h : P.par b = some a) : ¬ Anc P b a := by
  intro hab
  have key : ∀ {x y}, Anc P y x → Relation.ReflTransGen (fun a b => P.par b = some a ∨ P.par₂ b = some a) y x := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (Or.inl hstep) ih
  exact P.acyclic b (Relation.TransGen.tail' (key hab) (Or.inl h))

theorem Anc.eq_root {a : V} (h : Anc P a P.root) : a = P.root := by
  rcases h.eq_or_par with h | ⟨p, hp, -⟩
  · exact h.symm
  · rw [(P.par_eq_none P.root).2 rfl] at hp
    simp at hp

section Time

variable {t : V → EReal} (ht : ∀ v a, P.par v = some a → t a < t v)

include ht

theorem Anc.time_le {a b : V} (h : Anc P b a) : t b ≤ t a := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (ht _ _ hstep).le.trans ih

theorem Anc.time_lt {a b : V} (h : Anc P b a) (hne : b ≠ a) : t b < t a := by
  rcases h.eq_or_par with h' | ⟨p, hp, hr⟩
  · exact absurd h'.symm hne
  · exact (Anc.time_le ht hr).trans_lt (ht _ _ hp)

/-- On the path up from a node, the order of time is the order of the path. -/
theorem anc_of_time_le {a b c : V} (h₁ : Anc P a c) (h₂ : Anc P b c) (hle : t a ≤ t b) : Anc P a b := by
  rcases h₁.total h₂ with h | h
  · exact h
  · by_cases hne : b = a
    · rw [hne]
      exact Anc.refl a
    · exact absurd hle (not_le.2 (Anc.time_lt ht h hne))

end Time

end Chain

section Insert

variable {ι : Type*} {V : Type*} (P : PreNet ι V)

/-- The time of a new node. -/
def timeOpt (t : V → EReal) (τ : EReal) : Option V → EReal
  | none => τ
  | some v => t v

/-- A new node `x` just above `v`, on the arc from `u`: the parent of `v` is now `x`, and `x` has the parent `y`. If `y = u`, then `x` is an ordinary node on the arc. Otherwise `x` is a recombination node with parents `y` and `u`, with the label of `u`: it's the recombination of an ordered-SPR
operation. Sites stay where they are, and so all the labels of `P` stay as they are. -/
def insertAbove {v u : V} (hu : P.par v = some u) (y : V) (q : Option V) (hq : (q = none ∧ y = u) ∨ (q = some u ∧ y ≠ u))
    (t : V → EReal) (ht : ∀ w a, P.par w = some a → t a < t w) (ht₂ : ∀ w a, P.par₂ w = some a → t a < t w) (τ : EReal)
    (h₁ : t y < τ) (h₂ : t u < τ) (h₃ : τ < t v) : PreNet ι (Option V) where
  root := some P.root
  par := fun w => match w with
    | none => some (some y)
    | some w => if w = v then some none else (P.par w).map some
  par₂ := fun w => match w with
    | none => q.map some
    | some w => (P.par₂ w).map some
  site i := (P.site i).map some
  label := fun w => match w with
    | none => P.label u
    | some w => P.label w
  par_eq_none := by
    have hv : v ≠ P.root := fun h => by
      rw [h, (P.par_eq_none P.root).2 rfl] at hu
      simp at hu
    rintro (- | w)
    · simp
    · by_cases hw : w = v
      · subst hw
        simp [hv]
      · simp [hw, P.par_eq_none]
  par₂_root := by simp [P.par₂_root]
  par₂_ne := by
    rintro (- | w) a ha
    · rcases hq with ⟨rfl, -⟩ | ⟨rfl, hne⟩
      · simp at ha
      · simp only [Option.map_some, Option.some.injEq] at ha
        subst ha
        intro h'
        exact hne (Option.some_inj.1 (Option.some_inj.1 h'))
    · simp only [Option.map_eq_some_iff] at ha
      obtain ⟨q₀, hq₀, rfl⟩ := ha
      by_cases hw : w = v
      · simp [hw]
      · simp only [hw, ↓reduceIte]
        intro h'
        simp only [Option.map_eq_some_iff] at h'
        obtain ⟨p₀, hp₀, h''⟩ := h'
        exact P.par₂_ne w q₀ hq₀ (hp₀.trans (congrArg some (Option.some_inj.1 h'')))
  acyclic := by
    have hstrict : ∀ a b : Option V, ((match b with
        | none => some (some y)
        | some w => if w = v then some none else (P.par w).map some) = some a ∨ (match b with
        | none => q.map some
        | some w => (P.par₂ w).map some) = some a) → timeOpt t τ a < timeOpt t τ b := by
      rintro a (- | w) (hab | hab)
      · simp only [Option.some.injEq] at hab
        subst hab
        exact h₁
      · rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · simp at hab
        · simp only [Option.map_some, Option.some.injEq] at hab
          subst hab
          exact h₂
      · by_cases hw : w = v
        · subst hw
          simp only [↓reduceIte, Option.some.injEq] at hab
          subst hab
          exact h₃
        · simp only [hw, ↓reduceIte, Option.map_eq_some_iff] at hab
          obtain ⟨p₀, hp₀, rfl⟩ := hab
          exact ht _ _ hp₀
      · simp only [Option.map_eq_some_iff] at hab
        obtain ⟨p₀, hp₀, rfl⟩ := hab
        exact ht₂ _ _ hp₀
    exact acyclic_of_strict (timeOpt t τ) hstrict
  site_tree := by
    intro i w hw
    simp only [Option.map_eq_some_iff] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨h₄, h₅⟩ := P.site_tree i w' hw'
    simp [h₄, h₅]
  label_tree := by
    rintro (- | w) p hp hp₂ i
    · simp only [Option.some.injEq] at hp
      subst hp
      rcases hq with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · simp
      · simp at hp₂
    · have hw₂ : P.par₂ w = none := by simpa using hp₂
      by_cases hw : w = v
      · subst hw
        simp only [↓reduceIte, Option.some.injEq] at hp
        subst hp
        simp only [Option.map_eq_some_iff, Option.some.injEq, exists_eq_right]
        exact P.label_tree w u hu hw₂ i
      · simp only [hw, ↓reduceIte, Option.map_eq_some_iff] at hp
        obtain ⟨p₀, hp₀, rfl⟩ := hp
        simp only [Option.map_eq_some_iff, Option.some.injEq, exists_eq_right]
        exact P.label_tree w p₀ hp₀ hw₂ i
  label_recomb := by
    rintro (- | w) p a hp ha i
    · rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp at ha
      · simp only [Option.map_some, Option.some.injEq] at ha
        subst ha
        exact Or.inr rfl
    · simp only [Option.map_eq_some_iff] at ha
      obtain ⟨q₀, hq₀, rfl⟩ := ha
      by_cases hw : w = v
      · subst hw
        simp only [↓reduceIte, Option.some.injEq] at hp
        subst hp
        exact P.label_recomb w u q₀ hu hq₀ i
      · simp only [hw, ↓reduceIte, Option.map_eq_some_iff] at hp
        obtain ⟨p₀, hp₀, rfl⟩ := hp
        exact P.label_recomb w p₀ q₀ hp₀ hq₀ i

end Insert

theorem not_anc_v_y {ι V : Type*} {P : PreNet ι V} {v y : V} {t : V → EReal} (ht : ∀ w a, P.par w = some a → t a < t w) {τ : EReal} (h₁ : t y < τ) (h₃ : τ < t v) : ¬ Anc P v y :=
  fun h => absurd (Anc.time_le ht h) (not_le.2 (h₁.trans h₃))

section InsertAnc

variable {ι : Type*} {V : Type*} {P : PreNet ι V} {v u : V} {hu : P.par v = some u} {y : V} {q : Option V} {hq : (q = none ∧ y = u) ∨ (q = some u ∧ y ≠ u)}
  {t : V → EReal} {ht : ∀ w a, P.par w = some a → t a < t w} {ht₂ : ∀ w a, P.par₂ w = some a → t a < t w} {τ : EReal}
  {h₁ : t y < τ} {h₂ : t u < τ} {h₃ : τ < t v}

/-- The parent of an old node after `insertAbove`. -/
theorem par_insertAbove_ne {w : V} (hw : w ≠ v) : (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).par (some w) = (P.par w).map some := by
  change (if w = v then some none else (P.par w).map some) = _
  rw [ite_eq_right hw]

theorem par_insertAbove_self : (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).par (some v) = some none := by
  change (if v = v then some none else (P.par v).map some) = _
  rw [ite_eq_left rfl]

theorem par_insertAbove_none : (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).par none = some (some y) := rfl

/-- A path that avoids `v` stays. -/
theorem anc_insertAbove_of_not {n c : V} (hv : ¬ Anc P v c) (h : Anc P n c) :
    Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) (some n) (some c) := by
  induction h with
  | refl => exact Anc.refl _
  | @tail p n hp hstep ih =>
    have hpv : p ≠ v := fun h' => hv (h' ▸ hp)
    refine Relation.ReflTransGen.tail ih ?_
    rw [par_insertAbove_ne hpv, hstep]
    rfl

/-- A path up to a node at or below `v` stays. -/
theorem anc_insertAbove_below {n c : V} (hvn : Anc P v n) (h : Anc P n c) :
    Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) (some n) (some c) := by
  induction h with
  | refl => exact Anc.refl _
  | @tail p n _ hstep ih =>
    have hpv : p ≠ v := by
      rintro rfl
      exact not_anc_of_par (P := P) hstep hvn
    refine Relation.ReflTransGen.tail (ih (Anc.head hstep hvn)) ?_
    rw [par_insertAbove_ne hpv, hstep]
    rfl

/-- The new chain above a node `c` below `v`: up to `v`, then `x`, then the path up from `y`. -/
theorem anc_insertAbove_iff_of_mem {n c : V} (hvc : Anc P v c) :
    Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) (some n) (some c) ↔ (Anc P v n ∧ Anc P n c) ∨ Anc P n y := by
  constructor
  · intro h
    have key : ∀ z, Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) z (some c) → match z with
        | none => True
        | some n => (Anc P v n ∧ Anc P n c) ∨ Anc P n y := by
      intro z hz
      induction hz with
      | refl => exact Or.inl ⟨hvc, Anc.refl c⟩
      | @tail z₁ z₂ _ hstep ih =>
        rcases z₁ with - | w
        · rw [par_insertAbove_none] at hstep
          obtain rfl := Option.some_inj.1 hstep
          exact Or.inr (Anc.refl y)
        · by_cases hw : w = v
          · subst hw
            rw [par_insertAbove_self] at hstep
            obtain rfl := Option.some_inj.1 hstep
            trivial
          · rw [par_insertAbove_ne hw, Option.map_eq_some_iff] at hstep
            obtain ⟨p, hp, rfl⟩ := hstep
            rcases ih with ⟨h₄, h₅⟩ | h₄
            · rcases h₄.eq_or_par with h' | ⟨p', hp', hr⟩
              · exact absurd h' hw
              · obtain rfl := Option.some_inj.1 (hp.symm.trans hp')
                exact Or.inl ⟨hr, Anc.trans (Anc.of_par hp) h₅⟩
            · exact Or.inr (Anc.trans (Anc.of_par hp) h₄)
    exact key _ h
  · rintro (⟨h₄, h₅⟩ | h₄)
    · exact anc_insertAbove_below h₄ h₅
    · have h₅ := anc_insertAbove_of_not (hu := hu) (hq := hq) (ht := ht) (ht₂ := ht₂) (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (not_anc_v_y ht h₁ h₃) h₄
      have h₆ := anc_insertAbove_below (hu := hu) (hq := hq) (ht := ht) (ht₂ := ht₂) (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (Anc.refl v) hvc
      refine Relation.ReflTransGen.trans h₆ (Relation.ReflTransGen.head par_insertAbove_self (Relation.ReflTransGen.head par_insertAbove_none h₅))

/-- The chain above a node not below `v` doesn't change. -/
theorem anc_insertAbove_iff_of_not {n c : V} (hvc : ¬ Anc P v c) :
    Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) (some n) (some c) ↔ Anc P n c := by
  refine ⟨fun h => ?_, anc_insertAbove_of_not hvc⟩
  have key : ∀ z, Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) z (some c) → match z with
      | none => False
      | some n => Anc P n c := by
    intro z hz
    induction hz with
    | refl => exact Anc.refl c
    | @tail z₁ z₂ _ hstep ih =>
      rcases z₁ with - | w
      · exact ih.elim
      · by_cases hw : w = v
        · subst hw
          exact absurd ih hvc
        · rw [par_insertAbove_ne hw, Option.map_eq_some_iff] at hstep
          obtain ⟨p, hp, rfl⟩ := hstep
          exact Anc.trans (Anc.of_par hp) ih
  exact key _ h

theorem anc_insertAbove_none {c : V} : Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) none (some c) ↔ Anc P v c := by
  constructor
  · intro h
    by_contra hvc
    have key : ∀ z, Anc (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) z (some c) → match z with
        | none => False
        | some n => Anc P n c := by
      intro z hz
      induction hz with
      | refl => exact Anc.refl c
      | @tail z₁ z₂ _ hstep ih =>
        rcases z₁ with - | w
        · exact ih.elim
        · by_cases hw : w = v
          · subst hw
            exact absurd ih hvc
          · rw [par_insertAbove_ne hw, Option.map_eq_some_iff] at hstep
            obtain ⟨p, hp, rfl⟩ := hstep
            exact Anc.trans (Anc.of_par hp) ih
    exact key _ h
  · intro hvc
    exact Relation.ReflTransGen.tail (anc_insertAbove_below (Anc.refl v) hvc) par_insertAbove_self

theorem t_par_insertAbove : ∀ w a, (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).par w = some a → timeOpt t τ a < timeOpt t τ w := by
  rintro (- | w) a ha
  · rw [par_insertAbove_none] at ha
    obtain rfl := Option.some_inj.1 ha
    exact h₁
  · by_cases hw : w = v
    · subst hw
      rw [par_insertAbove_self] at ha
      obtain rfl := Option.some_inj.1 ha
      exact h₃
    · rw [par_insertAbove_ne hw, Option.map_eq_some_iff] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      exact ht _ _ hp

theorem t_par₂_insertAbove : ∀ w a, (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).par₂ w = some a → timeOpt t τ a < timeOpt t τ w := by
  rintro (- | w) a ha
  · change q.map some = some a at ha
    rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp at ha
    · simp only [Option.map_some, Option.some.injEq] at ha
      subst ha
      exact h₂
  · change (P.par₂ w).map some = some a at ha
    rw [Option.map_eq_some_iff] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact ht₂ _ _ hp

end InsertAnc

section State

variable {ι : Type*} {V : Type*} {X : Type*} [Fintype X] [DecidableEq X]

/-- The state of the construction: the arcs followed to the right of every crossover so far form the tree `T`, and a node at time `t n` on the path up from the row `r` has below it exactly the rows of the edge of `T` above `r` at that time. -/
structure Realizes (P : PreNet ι V) (t : V → EReal) (leaf : X → V) (T : TimeOrderedTree X) : Prop where
  t_par : ∀ v a, P.par v = some a → t a < t v
  t_par₂ : ∀ v a, P.par₂ v = some a → t a < t v
  t_root : t P.root = ⊥
  t_leaf : ∀ r, t (leaf r) = ⊤
  J : ∀ n r r', Anc P n (leaf r) → (Anc P n (leaf r') ↔ r' ∈ lin T r (t n))
  K : ∀ D ∈ T.clusters, ∃ n, ∃ r ∈ D, Anc P n (leaf r) ∧ t n = tm T D

variable {P : PreNet ι V} {t : V → EReal} {leaf : X → V} {T : TimeOrderedTree X}

/-- The node of a cluster has exactly its rows below it. -/
theorem Realizes.exists_node (R : Realizes P t leaf T) {D : Finset X} (hD : D ∈ T.clusters) :
    ∃ n, t n = tm T D ∧ ∀ r, Anc P n (leaf r) ↔ r ∈ D := by
  obtain ⟨n, r, hr, han, htn⟩ := R.K D hD
  refine ⟨n, htn, fun r' => ?_⟩
  rw [R.J n r r' han, htn, lin_tm hD hr]

/-- A node isn't the root, unless its time is `⊥`. -/
theorem Realizes.ne_root (R : Realizes P t leaf T) {n : V} (h : t n ≠ ⊥) : n ≠ P.root := fun hn => h (hn ▸ R.t_root)

/-- Nothing new at a time between a node and its parent. -/
theorem Realizes.lin_eq_of_between (R : Realizes P t leaf T) {v u : V} (hu : P.par v = some u) {r : X} (hr : Anc P v (leaf r)) {τ : EReal}
    (h₁ : t u < τ) (h₂ : τ < t v) : lin T r τ = lin T r (t v) := by
  refine IsLin.lin_eq ⟨?_, ?_, ?_, ?_⟩
  · exact (isLin_lin T r (t v)).mem
  · exact (isLin_lin T r (t v)).mem_row
  · exact h₂.le.trans (isLin_lin T r (t v)).le_tm
  · intro D' hD' hr' hτ
    obtain ⟨e, r₁, hr₁, he, hte⟩ := R.K D' hD'
    have hrm : Anc P e (leaf r) := by
      rw [R.J e r₁ r he, hte, lin_tm hD' hr₁]
      exact hr'
    have : t v ≤ tm T D' := by
      rcases hrm.total hr with h | h
      · rcases h.eq_or_par with h' | ⟨p, hp, hr₂⟩
        · rw [h']
          exact hte.le
        · obtain rfl := Option.some_inj.1 (hp.symm.trans hu)
          exact absurd (hte ▸ Anc.time_le R.t_par hr₂) (not_le.2 (h₁.trans_le hτ))
      · rw [← hte]
        exact Anc.time_le R.t_par h
    exact (isLin_lin T r (t v)).max D' hD' hr' this

/-- Where a time falls on the path up from a row: at a node, or strictly between a node and its parent. -/
theorem Realizes.exists_crossing [Finite V] (R : Realizes P t leaf T) (r₀ : X) (τ : EReal) :
    (∃ n, Anc P n (leaf r₀) ∧ t n = τ) ∨ ∃ b a, Anc P b (leaf r₀) ∧ P.par b = some a ∧ t a < τ ∧ τ < t b := by
  by_cases hex : ∃ n, Anc P n (leaf r₀) ∧ t n = τ
  · exact Or.inl hex
  · right
    push Not at hex
    have hne : {n | Anc P n (leaf r₀) ∧ τ ≤ t n}.Nonempty := ⟨leaf r₀, Anc.refl _, by rw [R.t_leaf]; exact le_top⟩
    obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image (Set.toFinite _).toFinset t (Set.Finite.toFinset_nonempty _ |>.2 hne)
    obtain ⟨hb₁, hb₂⟩ := (Set.Finite.mem_toFinset _).1 hb
    have hb₃ : τ < t b := lt_of_le_of_ne hb₂ (hex b hb₁).symm
    have hbroot : b ≠ P.root := R.ne_root (ne_bot_of_gt hb₃)
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 fun h => hbroot ((P.par_eq_none b).1 h)
    refine ⟨b, a, hb₁, ha, ?_, hb₃⟩
    by_contra hle
    have hle' : τ ≤ t a := not_lt.1 hle
    have ha₁ : Anc P a (leaf r₀) := Anc.trans (Anc.of_par ha) hb₁
    exact absurd (hmin a ((Set.Finite.mem_toFinset _).2 ⟨ha₁, hle'⟩)) (not_le.2 (R.t_par _ _ ha))

/-- A new node on an arc, at a time strictly between its ends, keeps the state. -/
theorem Realizes.insertAbove_same (R : Realizes P t leaf T) {v u : V} (hu : P.par v = some u) {τ : EReal} (h₂ : t u < τ) (h₃ : τ < t v) :
    Realizes (insertAbove P hu u none (Or.inl ⟨rfl, rfl⟩) t R.t_par R.t_par₂ τ h₂ h₂ h₃) (timeOpt t τ) (fun r => some (leaf r)) T := by
  have hanc : ∀ n c, Anc (insertAbove P hu u none (Or.inl ⟨rfl, rfl⟩) t R.t_par R.t_par₂ τ h₂ h₂ h₃) (some n) (some c) ↔ Anc P n c := by
    intro n c
    by_cases hvc : Anc P v c
    · rw [anc_insertAbove_iff_of_mem hvc]
      constructor
      · rintro (⟨-, h⟩ | h)
        · exact h
        · exact Anc.trans h (Anc.trans (Anc.of_par hu) hvc)
      · intro h
        rcases h.total hvc with h' | h'
        · rcases h'.eq_or_par with h'' | ⟨p, hp, hr⟩
          · subst h''
            exact Or.inl ⟨Anc.refl _, hvc⟩
          · obtain rfl := Option.some_inj.1 (hp.symm.trans hu)
            exact Or.inr hr
        · exact Or.inl ⟨h', h⟩
    · exact anc_insertAbove_iff_of_not hvc
  refine ⟨t_par_insertAbove, t_par₂_insertAbove, R.t_root, R.t_leaf, ?_, ?_⟩
  · rintro (- | n) r r' hn
    · have hvr := anc_insertAbove_none.1 hn
      rw [anc_insertAbove_none]
      change Anc P v (leaf r') ↔ r' ∈ lin T r τ
      rw [R.lin_eq_of_between hu hvr h₂ h₃]
      exact R.J v r r' hvr
    · rw [hanc] at hn ⊢
      exact R.J n r r' hn
  · intro D hD
    obtain ⟨n, r, hr, han, htn⟩ := R.K D hD
    exact ⟨some n, r, hr, (hanc _ _).2 han, htn⟩

end State

section SPRStep

variable {ι : Type*} {V : Type*} {X : Type*} [Fintype X] [DecidableEq X] {P : PreNet ι V} {t : V → EReal} {leaf : X → V} {T T' : TimeOrderedTree X} {A : Finset X}

/-- A cluster of `T'` that isn't within `A` and isn't the new parent of `A` is the node that stays of its pruned cluster. -/
theorem retained_sdiff {T' : TimeOrderedTree X} (hA : A ∈ T'.clusters) {P' : Finset X} (hP' : P' ∈ T'.clusters) (hAP : A ⊂ P') (hmin : ∀ E ∈ T'.clusters, A ⊂ E → P' ⊆ E)
    {D' : Finset X} (hD' : D' ∈ T'.clusters) (hDA : ¬ D' ⊆ A) (hne : D' ≠ P') : retained T' A (D' \ A) = D' := by
  have hAne := T'.isHierarchy.2.2.1 A hA
  unfold retained
  rcases T'.isHierarchy.2.2.2 D' hD' A hA with h | h | h
  · exact absurd h hDA
  · have hAD : A ⊂ D' := h.ssubset_of_ne fun h' => hDA h'.ge
    split_ifs with hG
    · exfalso
      have hsub := hmin D' hD' hAD
      obtain ⟨r₀, hr₀, hr₀A⟩ := Finset.exists_of_ssubset hAP
      have hr₀G : r₀ ∈ D' \ A := Finset.mem_sdiff.2 ⟨hsub hr₀, hr₀A⟩
      rcases comparable_of_mem hP' hG hr₀ hr₀G with h₁ | h₁
      · obtain ⟨a, ha⟩ := hAne
        exact (Finset.mem_sdiff.1 (h₁ (hAP.subset ha))).2 ha
      · refine hne (hsub.antisymm' ?_)
        intro x hx
        by_cases hxA : x ∈ A
        · exact hAP.subset hxA
        · exact h₁ (Finset.mem_sdiff.2 ⟨hx, hxA⟩)
    · exact Finset.sdiff_union_of_subset h
  · rw [h.sdiff_eq_left, ite_eq_left hD']

/-- **One ordered-SPR operation** keeps the state, with the tree `T'` in place of `T`, when a recombination node `x` is inserted just above the node of the pruned subtree, its new parent being a node `w` at the time of the new parent of `A`. -/
theorem Realizes.spr (R : Realizes P t leaf T) (hs : SPRAt T T' A) {nA u w : V} (hu : P.par nA = some u) (hnt : t nA = tm T A) (hnr : ∀ r, Anc P nA (leaf r) ↔ r ∈ A)
    {P' : Finset X} (hP' : P' ∈ T'.clusters) (hAP : A ⊂ P') (hmin : ∀ E ∈ T'.clusters, A ⊂ E → P' ⊆ E) {r₀ : X} (hr₀ : r₀ ∈ P') (hr₀A : r₀ ∉ A) (hw : Anc P w (leaf r₀)) (htw : t w = tm T' P')
    {q : Option V} (hq : (q = none ∧ w = u) ∨ (q = some u ∧ w ≠ u)) {τ : EReal} (h₁ : t w < τ) (h₂ : t u < τ) (h₃ : τ < t nA) :
    Realizes (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) (timeOpt t τ) (fun r => some (leaf r)) T' := by
  have hAne : A.Nonempty := T'.isHierarchy.2.2.1 A hs.mem'
  have htA : t nA = tm T' A := hnt.trans (hs.tm_eq subset_rfl hs.mem)
  have hPle : ∀ E ∈ T'.clusters, A ⊂ E → tm T' E ≤ t w := fun E hE hAE => htw ▸ tm_le_of_subset hP' hE (hmin E hE hAE)
  have hancA : ∀ n r, r ∈ A → (Anc (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) (some n) (some (leaf r)) ↔ (Anc P nA n ∧ Anc P n (leaf r)) ∨ Anc P n w) :=
    fun n r hr => anc_insertAbove_iff_of_mem ((hnr r).2 hr)
  have hancN : ∀ n r, r ∉ A → (Anc (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) (some n) (some (leaf r)) ↔ Anc P n (leaf r)) :=
    fun n r hr => anc_insertAbove_iff_of_not fun h => hr ((hnr r).1 h)
  have hancX : ∀ r, Anc (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) none (some (leaf r)) ↔ r ∈ A :=
    fun r => anc_insertAbove_none.trans (hnr r)
  refine ⟨t_par_insertAbove, t_par₂_insertAbove, R.t_root, R.t_leaf, ?_, ?_⟩
  · rintro (- | n) r r' hn
    · have hr := (hancX r).1 hn
      have hlin : lin T' r τ = A := by
        refine IsLin.lin_eq ⟨hs.mem', hr, htA ▸ h₃.le, fun D' hD' hr' hτ => ?_⟩
        rcases comparable_of_mem hD' hs.mem' hr' hr with h | h
        · exact h
        · rcases h.eq_or_ssubset with h'' | h''
          · exact h''.ge
          · exact absurd hτ (not_le.2 ((hPle D' hD' h'').trans_lt h₁))
      rw [hancX]
      change r' ∈ A ↔ r' ∈ lin T' r τ
      rw [hlin]
    · by_cases hN1 : Anc P nA n
      · have hle : t nA ≤ t n := Anc.time_le R.t_par hN1
        have hnotw : ¬ Anc P n w := fun h => absurd ((Anc.time_le R.t_par h).trans_lt (h₁.trans h₃)) (not_lt.2 hle)
        have hiff : ∀ r₁, Anc (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) (some n) (some (leaf r₁)) ↔ Anc P n (leaf r₁) := by
          intro r₁
          by_cases hr₁ : r₁ ∈ A
          · rw [hancA n r₁ hr₁]
            constructor
            · rintro (⟨-, h⟩ | h)
              · exact h
              · exact absurd h hnotw
            · exact fun h => Or.inl ⟨hN1, h⟩
          · exact hancN n r₁ hr₁
        rw [hiff] at hn ⊢
        have hr : r ∈ A := (hnr r).1 (Anc.trans hN1 hn)
        have hlin : lin T r (t n) = lin T' r (t n) := by
          refine hs.lin_eq_of_mem hr (fun E hE hAE => ?_) (fun E hE hAE => ?_)
          · refine (tm_lt_of_ssubset hs.mem hE hAE).trans_le ?_
            rw [← hnt]
            exact hle
          · refine (tm_lt_of_ssubset hs.mem' hE hAE).trans_le ?_
            rw [← htA]
            exact hle
        change _ ↔ r' ∈ lin T' r (t n)
        rw [← hlin]
        exact R.J n r r' hn
      · by_cases hN2 : Anc P n w
        · have hnr₀ : Anc P n (leaf r₀) := Anc.trans hN2 hw
          have htn : t n ≤ tm T' P' := htw ▸ Anc.time_le R.t_par hN2
          have hiff : ∀ r₁, Anc (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) (some n) (some (leaf r₁)) ↔ r₁ ∈ lin T' r₀ (t n) := by
            intro r₁
            by_cases hr₁ : r₁ ∈ A
            · rw [hancA n r₁ hr₁]
              exact ⟨fun _ => subset_lin hP' hr₀ htn (hAP.subset hr₁), fun _ => Or.inr hN2⟩
            · rw [hancN n r₁ hr₁, R.J n r₀ r₁ hnr₀]
              exact hs.mem_lin_iff hr₀A hr₁ _
          rw [hiff] at hn ⊢
          change _ ↔ r' ∈ lin T' r (t n)
          rw [lin_eq_of_mem hn]
        · have hfalse : ∀ r₁, r₁ ∈ A → ¬ Anc (insertAbove P hu w q hq t R.t_par R.t_par₂ τ h₁ h₂ h₃) (some n) (some (leaf r₁)) := by
            intro r₁ hr₁ h
            rcases (hancA n r₁ hr₁).1 h with ⟨h', -⟩ | h'
            · exact hN1 h'
            · exact hN2 h'
          have hrA : r ∉ A := fun h => hfalse r h hn
          have hnr' : Anc P n (leaf r) := (hancN n r hrA).1 hn
          change _ ↔ r' ∈ lin T' r (t n)
          constructor
          · intro h
            have hr'A : r' ∉ A := fun h' => hfalse r' h' h
            exact (hs.mem_lin_iff hrA hr'A _).1 ((R.J n r r' hnr').1 ((hancN n r' hr'A).1 h))
          · intro h
            by_cases hr'A : r' ∈ A
            · exfalso
              have hl := isLin_lin T' r (t n)
              have hAE : A ⊂ lin T' r (t n) := by
                rcases comparable_of_mem hs.mem' hl.mem hr'A h with h₄ | h₄
                · exact h₄.ssubset_of_ne fun h₅ => hrA (h₅.symm ▸ hl.mem_row)
                · exact absurd (h₄ hl.mem_row) hrA
              have hPE := hmin _ hl.mem hAE
              have htn : t n ≤ t w := hl.le_tm.trans (hPle _ hl.mem hAE)
              have hr₀E : r₀ ∈ lin T' r (t n) := hPE hr₀
              have hnr₀ : Anc P n (leaf r₀) := (R.J n r r₀ hnr').2 ((hs.mem_lin_iff hrA hr₀A _).2 hr₀E)
              exact hN2 (anc_of_time_le R.t_par hnr₀ hw htn)
            · exact (hancN n r' hr'A).2 ((R.J n r r' hnr').2 ((hs.mem_lin_iff hrA hr'A _).2 h))
  · intro D' hD'
    by_cases hDA : D' ⊆ A
    · have hD'T := (hs.sub D' hDA).2 hD'
      obtain ⟨n, r, hr, han, htn⟩ := R.K D' hD'T
      refine ⟨some n, r, hr, ?_, htn.trans (hs.tm_eq hDA hD'T)⟩
      refine (hancA n r (hDA hr)).2 (Or.inl ⟨anc_of_time_le R.t_par ((hnr r).2 (hDA hr)) han ?_, han⟩)
      rw [hnt, htn]
      exact tm_le_of_subset hD'T hs.mem hDA
    · by_cases hDP : D' = P'
      · subst hDP
        exact ⟨some w, r₀, hr₀, (hancN w r₀ hr₀A).2 hw, htw⟩
      · obtain ⟨r, hr, hrA⟩ := Finset.not_subset.1 hDA
        have hGT' : D' \ A ∈ T'.prunedClusters A := Finset.mem_image.2 ⟨D', Finset.mem_filter.2 ⟨hD', hDA⟩, rfl⟩
        have hGT : D' \ A ∈ T.prunedClusters A := hs.pr ▸ hGT'
        have hret := retained_sdiff hs.mem' hP' hAP hmin hD' hDA hDP
        have hE := retained_mem hs.mem hGT
        obtain ⟨m, htm, hrows⟩ := R.exists_node hE
        refine ⟨some m, r, hr, (hancN m r hrA).2 ((hrows r).2 (subset_retained _ (Finset.mem_sdiff.2 ⟨hr, hrA⟩))), htm.trans ?_⟩
        by_cases hc : 2 ≤ (D' \ A).card
        · rw [tm_retained hc, hs.prt _ hGT hc, ← tm_retained hc, hret]
        · have hG1 : D' \ A = {r} := by
            have hrG := Finset.mem_sdiff.2 ⟨hr, hrA⟩
            have hpos := Finset.card_pos.2 ⟨r, hrG⟩
            exact Finset.eq_singleton_iff_unique_mem.2 ⟨hrG, fun x hx => Finset.card_le_one.1 (by omega) x hx r hrG⟩
          have h₄ : retained T A (D' \ A) = D' \ A := by
            unfold retained
            rw [hG1, ite_eq_left (T.isHierarchy.2.1 r)]
          have h₅ : retained T' A (D' \ A) = D' \ A := by
            unfold retained
            rw [hG1, ite_eq_left (T'.isHierarchy.2.1 r)]
          rw [h₄, ← hret, h₅]
          simp [tm, hc]

end SPRStep

section Labels

variable {ι : Type*} [LinearOrder ι] {V : Type*} {X : Type*}

/-- The sites placed so far are `U`, the others are still constant, the rows have their states at the sites placed, and a recombination takes a prefix of sites placed from one parent. -/
structure Labelled (P : PreNet ι V) (leaf : X → V) (S : ι → Bool) (U : LowerSet ι) (A : X → ι → Bool) : Prop where
  root : P.label P.root = S
  site : ∀ i, (∃ v, P.site i = some v) ↔ i ∈ U
  const : ∀ i, i ∉ U → ∀ v, P.label v i = S i
  rows : ∀ i, i ∈ U → ∀ r, P.label (leaf r) i = A r i
  obey : ∀ x p q, P.par x = some p → P.par₂ x = some q → ∃ L : LowerSet ι, (∀ i ∈ L, i ∈ U) ∧ ∀ i, P.label x i = if i ∈ L then P.label q i else P.label p i

variable {P : PreNet ι V} {leaf : X → V} {S : ι → Bool} {U : LowerSet ι} {A : X → ι → Bool}

/-- The labels stay under `insertAbove`. -/
theorem Labelled.insertAbove (hL : Labelled P leaf S U A) {v u y : V} (hu : P.par v = some u) {q : Option V} (hq : (q = none ∧ y = u) ∨ (q = some u ∧ y ≠ u))
    {t : V → EReal} (ht : ∀ w a, P.par w = some a → t a < t w) (ht₂ : ∀ w a, P.par₂ w = some a → t a < t w) {τ : EReal} (h₁ : t y < τ) (h₂ : t u < τ) (h₃ : τ < t v) :
    Labelled (SongHein2005.insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃) (fun r => some (leaf r)) S U A where
  root := hL.root
  site i := by
    rw [← hL.site i]
    constructor
    · rintro ⟨w, hw⟩
      change (P.site i).map some = some w at hw
      rw [Option.map_eq_some_iff] at hw
      obtain ⟨w', hw', -⟩ := hw
      exact ⟨w', hw'⟩
    · rintro ⟨w, hw⟩
      exact ⟨some w, by change (P.site i).map some = some (some w); rw [hw]; rfl⟩
  const i hi w := by
    rcases w with - | w
    · exact hL.const i hi u
    · exact hL.const i hi w
  rows := hL.rows
  obey := by
    rintro (- | x) p a hp ha
    · rw [par_insertAbove_none] at hp
      obtain rfl := Option.some_inj.1 hp
      change q.map some = some a at ha
      rcases hq with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp at ha
      · obtain rfl := Option.some_inj.1 ha
        refine ⟨U, fun _ h => h, fun i => ?_⟩
        by_cases hi : i ∈ U
        · rw [ite_eq_left hi]
          rfl
        · rw [ite_eq_right hi]
          exact (hL.const i hi u).trans (hL.const i hi y).symm
    · change (P.par₂ x).map some = some a at ha
      rw [Option.map_eq_some_iff] at ha
      obtain ⟨a', ha', rfl⟩ := ha
      by_cases hx : x = v
      · subst hx
        rw [par_insertAbove_self] at hp
        obtain rfl := Option.some_inj.1 hp
        exact hL.obey x u a' hu ha'
      · rw [par_insertAbove_ne hx, Option.map_eq_some_iff] at hp
        obtain ⟨p', hp', rfl⟩ := hp
        exact hL.obey x p' a' hp' ha'

omit [LinearOrder ι] in
theorem anc_iff_of_par {P : PreNet ι V} {b v p : V} (hp : P.par v = some p) (hne : v ≠ b) : Anc P b v ↔ Anc P b p := by
  constructor
  · intro h
    rcases h.eq_or_par with h' | ⟨p', hp', hr⟩
    · exact absurd h' hne
    · rwa [Option.some_inj.1 (hp.symm.trans hp')]
  · exact Anc.head hp

/-- Placing the site `i` on the arc into the node `b`: the state of `i` is changed at `b` and at the nodes that reach `b` by arcs to the right of every crossover so far, as `i` is to the right of them. -/
def addSite (P : PreNet ι V) (b : V) (hb₁ : P.par₂ b = none) (hb₂ : b ≠ P.root) (i : ι) (s : Bool) : PreNet ι V where
  root := P.root
  par := P.par
  par₂ := P.par₂
  site j := if j = i then some b else P.site j
  label v j := if j = i then (if Anc P b v then !s else s) else P.label v j
  par_eq_none := P.par_eq_none
  par₂_root := P.par₂_root
  par₂_ne := P.par₂_ne
  acyclic := P.acyclic
  site_tree j v hv := by
    by_cases hj : j = i
    · rw [ite_eq_left hj] at hv
      obtain rfl := Option.some_inj.1 hv
      exact ⟨hb₁, hb₂⟩
    · rw [ite_eq_right hj] at hv
      exact P.site_tree j v hv
  label_tree v p hp hv j := by
    by_cases hj : j = i
    · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left hj]
      by_cases hvb : v = b
      · subst hvb
        have hnot : ¬ Anc P v p := not_anc_of_par hp
        rw [ite_eq_left (Anc.refl v), ite_eq_left rfl, ite_eq_right hnot]
      · have hne : some b ≠ some v := fun h => hvb (Option.some_inj.1 h).symm
        rw [ite_eq_right hne]
        simp only [anc_iff_of_par hp hvb]
    · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right hj]
      exact P.label_tree v p hp hv j
  label_recomb v p q hp hq j := by
    by_cases hj : j = i
    · have hvb : v ≠ b := by
        rintro rfl
        rw [hb₁] at hq
        simp at hq
      left
      rw [ite_eq_left hj, ite_eq_left hj]
      simp only [anc_iff_of_par hp hvb]
    · rw [ite_eq_right hj, ite_eq_right hj]
      · rw [ite_eq_right hj]
        exact P.label_recomb v p q hp hq j

/-- The labels after placing a site. -/
theorem Labelled.addSite (hL : Labelled P leaf S U A) {b : V} (hb₁ : P.par₂ b = none) (hb₂ : b ≠ P.root) {i : ι} (hiU : i ∉ U) {U' : LowerSet ι} (hU' : ∀ j, j ∈ U' ↔ j ∈ U ∨ j = i)
    (hrows : ∀ r, A r i = if Anc P b (leaf r) then !S i else S i) :
    Labelled (SongHein2005.addSite P b hb₁ hb₂ i (S i)) leaf S U' A where
  root := by
    funext j
    change (if j = i then (if Anc P b P.root then !S i else S i) else P.label P.root j) = S j
    by_cases hj : j = i
    · subst hj
      rw [ite_eq_left rfl, ite_eq_right fun h => hb₂ h.eq_root]
    · rw [ite_eq_right hj, hL.root]
  site j := by
    change (∃ v, (if j = i then some b else P.site j) = some v) ↔ _
    rw [hU']
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, ↓reduceIte, or_false]
      exact hL.site j
  const j hj v := by
    rw [hU'] at hj
    push Not at hj
    change (if j = i then _ else P.label v j) = S j
    rw [ite_eq_right hj.2]
    exact hL.const j hj.1 v
  rows j hj r := by
    change (if j = i then (if Anc P b (leaf r) then !S i else S i) else P.label (leaf r) j) = A r j
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl, hrows]
    · rw [ite_eq_right hji]
      exact hL.rows j (((hU' j).1 hj).resolve_right hji) r
  obey x p q hp hq := by
    have hp' : P.par x = some p := hp
    have hq' : P.par₂ x = some q := hq
    obtain ⟨L, hLU, hLx⟩ := hL.obey x p q hp' hq'
    refine ⟨L, fun j hj => (hU' j).2 (Or.inl (hLU j hj)), fun j => ?_⟩
    change (if j = i then (if Anc P b x then !S i else S i) else P.label x j) = if j ∈ L then (if j = i then (if Anc P b q then !S i else S i) else P.label q j) else (if j = i then (if Anc P b p then !S i else S i) else P.label p j)
    by_cases hji : j = i
    · subst hji
      have hnot : j ∉ L := fun h => hiU (hLU j h)
      have hxb : x ≠ b := by
        rintro rfl
        rw [hb₁] at hq'
        simp at hq'
      rw [ite_eq_right hnot, ite_eq_left rfl, ite_eq_left rfl]
      simp only [anc_iff_of_par hp' hxb]
    · rw [ite_eq_right hji, ite_eq_right hji, ite_eq_right hji]
      exact hLx j

end Labels

section Steps

universe w

variable {ι : Type*} [LinearOrder ι] {X : Type w} [Fintype X] [DecidableEq X]

/-- A state of the construction for the tree `T`, the sites `U` placed, and at most `k` recombination nodes. -/
def HasState (T : TimeOrderedTree X) (S : ι → Bool) (U : LowerSet ι) (A : X → ι → Bool) (k : ℕ) : Prop :=
  ∃ (V : Type w) (_ : Finite V) (P : PreNet ι V) (t : V → EReal) (leaf : X → V), Realizes P t leaf T ∧ Labelled P leaf S U A ∧ P.recombCount ≤ k

section Count

variable {V : Type*} [Finite V] {P : PreNet ι V} {v u y : V} {hu : P.par v = some u} {q : Option V} {hq : (q = none ∧ y = u) ∨ (q = some u ∧ y ≠ u)}
  {t : V → EReal} {ht : ∀ w a, P.par w = some a → t a < t w} {ht₂ : ∀ w a, P.par₂ w = some a → t a < t w} {τ : EReal}
  {h₁ : t y < τ} {h₂ : t u < τ} {h₃ : τ < t v}

omit [LinearOrder ι] in
theorem recombCount_insertAbove_le : (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).recombCount ≤ P.recombCount + 1 := by
  have hsub : {x | (insertAbove P hu y q hq t ht ht₂ τ h₁ h₂ h₃).par₂ x ≠ none} ⊆ some '' {x | P.par₂ x ≠ none} ∪ {none} := by
    rintro (- | w) hx
    · exact Or.inr rfl
    · refine Or.inl ⟨w, fun h' => hx ?_, rfl⟩
      change (P.par₂ w).map some = none
      rw [h']
      rfl
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_union_le _ _).trans ?_)
  rw [Set.ncard_image_of_injective _ (Option.some_injective _), Set.ncard_singleton]
  rfl

omit [LinearOrder ι] in
theorem recombCount_insertAbove_same {hq : ((none : Option V) = none ∧ y = u) ∨ ((none : Option V) = some u ∧ y ≠ u)} : (insertAbove P hu y none hq t ht ht₂ τ h₁ h₂ h₃).recombCount ≤ P.recombCount := by
  have hsub : {x | (insertAbove P hu y none hq t ht ht₂ τ h₁ h₂ h₃).par₂ x ≠ none} ⊆ some '' {x | P.par₂ x ≠ none} := by
    rintro (- | w) hx
    · exact absurd rfl hx
    · refine ⟨w, fun h' => hx ?_, rfl⟩
      change (P.par₂ w).map some = none
      rw [h']
      rfl
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  rw [Set.ncard_image_of_injective _ (Option.some_injective _)]
  rfl

end Count

variable {T T' : TimeOrderedTree X} {S : ι → Bool} {U : LowerSet ι} {A : X → ι → Bool} {k : ℕ}

/-- The state doesn't depend on what isn't in the tree. -/
theorem HasState.same (h : T.Same T') (hst : HasState T S U A k) : HasState T' S U A k := by
  obtain ⟨V, hV, P, t, leaf, R, hL, hc⟩ := hst
  have htm : ∀ D ∈ T.clusters, tm T D = tm T' D := fun D hD => by
    unfold tm
    split_ifs with hc'
    · rw [h.2 D hD hc']
    · rfl
  have hlin : ∀ r τ, lin T r τ = lin T' r τ := fun r τ => by
    have hl := isLin_lin T r τ
    refine (IsLin.lin_eq ⟨h.1 ▸ hl.mem, hl.mem_row, htm _ hl.mem ▸ hl.le_tm, fun D' hD' hr hτ => ?_⟩).symm
    have hD'T : D' ∈ T.clusters := h.1 ▸ hD'
    exact hl.max D' hD'T hr (by rw [htm D' hD'T]; exact hτ)
  refine ⟨V, hV, P, t, leaf, ⟨R.t_par, R.t_par₂, R.t_root, R.t_leaf, fun n r r' hn => ?_, fun D hD => ?_⟩, hL, hc⟩
  · rw [← hlin]
    exact R.J n r r' hn
  · have hDT : D ∈ T.clusters := h.1 ▸ hD
    obtain ⟨n, r, hr, han, htn⟩ := R.K D hDT
    exact ⟨n, r, hr, han, htn.trans (htm D hDT)⟩

/-- A new node on the path up from a row, at any time that isn't taken. -/
theorem exists_node_at {V : Type w} [Finite V] {P : PreNet ι V} {t : V → EReal} {leaf : X → V} (R : Realizes P t leaf T) (hL : Labelled P leaf S U A) (r₀ : X) (τ : EReal) :
    ∃ (V' : Type w) (_ : Finite V') (P' : PreNet ι V') (t' : V' → EReal) (leaf' : X → V') (w : V'), Realizes P' t' leaf' T ∧ Labelled P' leaf' S U A ∧ P'.recombCount ≤ P.recombCount ∧
      Anc P' w (leaf' r₀) ∧ t' w = τ := by
  rcases R.exists_crossing r₀ τ with ⟨n, hn, htn⟩ | ⟨b, a, hb, ha, h₁, h₂⟩
  · exact ⟨V, inferInstance, P, t, leaf, n, R, hL, le_rfl, hn, htn⟩
  · exact ⟨Option V, inferInstance, _, timeOpt t τ, fun r => some (leaf r), none, R.insertAbove_same ha h₁ h₂, hL.insertAbove ha _ _ _ h₁ h₁ h₂, recombCount_insertAbove_same,
      anc_insertAbove_none.2 hb, rfl⟩

/-- **One ordered-SPR operation is one recombination node** (`ext:song_hein_step`). -/
theorem HasState.spr (hs : T.IsOrderedSPR T') (hst : HasState T S U A k) : HasState T' S U A (k + 1) := by
  obtain ⟨A₀, hA₀, hA₀', hne, hsub, htime, hpr, hprt⟩ := hs
  have hS : SPRAt T T' A₀ := ⟨hA₀, hA₀', hne, hsub, htime, hpr, hprt⟩
  obtain ⟨V₀, _, P₀, t₀, leaf₀, R₀, hL₀, hc₀⟩ := hst
  have hA₀ne : A₀.Nonempty := T'.isHierarchy.2.2.1 A₀ hA₀'
  obtain ⟨P', hP', hAP, hmin⟩ := exists_parent (T := T') hne
  have hmin' : ∀ E ∈ T'.clusters, A₀ ⊂ E → P' ⊆ E := fun E hE hAE => hmin E hE hAE hA₀ne
  obtain ⟨r₀, hr₀, hr₀A⟩ := Finset.exists_of_ssubset hAP
  obtain ⟨V, _, P, t, leaf, w, R, hL, hc, hw, htw⟩ := exists_node_at R₀ hL₀ r₀ (tm T' P')
  obtain ⟨nA, hnt, hnr⟩ := R.exists_node hA₀
  have hnroot : nA ≠ P.root := R.ne_root (hnt ▸ tm_ne_bot A₀)
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 fun h => hnroot ((P.par_eq_none nA).1 h)
  have hwlt : t w < t nA := by
    rw [htw, hnt, hS.tm_eq subset_rfl hA₀]
    exact tm_lt_of_ssubset hA₀' hP' hAP
  have hult : t u < t nA := R.t_par _ _ hu
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_between (max_lt hwlt hult)
  have h₁ : t w < τ := (le_max_left _ _).trans_lt hτ₁
  have h₂ : t u < τ := (le_max_right _ _).trans_lt hτ₁
  have hq : ∃ q : Option V, (q = none ∧ w = u) ∨ (q = some u ∧ w ≠ u) := by
    by_cases hwu : w = u
    · exact ⟨none, Or.inl ⟨rfl, hwu⟩⟩
    · exact ⟨some u, Or.inr ⟨rfl, hwu⟩⟩
  obtain ⟨q, hq⟩ := hq
  exact ⟨Option V, inferInstance, _, timeOpt t τ, fun r => some (leaf r), R.spr hS hu hnt hnr hP' hAP hmin' hr₀ hr₀A hw htw hq h₁ h₂ hτ₂, hL.insertAbove hu hq _ _ h₁ h₂ hτ₂,
    recombCount_insertAbove_le.trans (Nat.add_le_add_right (hc.trans hc₀) 1)⟩

/-- A chain of ordered-SPR operations. -/
theorem HasState.steps {j : ℕ} (hs : TimeOrderedTree.SPRSteps j T T') (hst : HasState T S U A k) : HasState T' S U A (k + j) := by
  induction j generalizing T k with
  | zero => exact hst.same hs
  | succ j ih =>
    obtain ⟨T₁, h₁, h₂⟩ := hs
    have := ih h₂ (hst.spr h₁)
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact this

/-- **Placing a site on the edge of the current tree above a cluster**, whose rows are those with the state other than `S i`. -/
theorem HasState.addSite {C : Finset X} (hC : C ∈ T.clusters) {i : ι} (hi : i ∉ U) {U' : LowerSet ι} (hU' : ∀ j, j ∈ U' ↔ j ∈ U ∨ j = i) (hrows : ∀ r, r ∈ C ↔ A r i = !S i)
    (hst : HasState T S U A k) : HasState T S U' A k := by
  obtain ⟨V, _, P, t, leaf, R, hL, hc⟩ := hst
  obtain ⟨n, htn, hnr⟩ := R.exists_node hC
  have hnroot : n ≠ P.root := R.ne_root (htn ▸ tm_ne_bot C)
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 fun h => hnroot ((P.par_eq_none n).1 h)
  obtain ⟨τ, h₁, h₂⟩ := exists_between (R.t_par _ _ hu)
  have R₁ := R.insertAbove_same hu h₁ h₂
  have hL₁ := hL.insertAbove hu (Or.inl ⟨rfl, rfl⟩) R.t_par R.t_par₂ h₁ h₁ h₂
  set P₁ := insertAbove P hu u none (Or.inl ⟨rfl, rfl⟩) t R.t_par R.t_par₂ τ h₁ h₁ h₂ with hP₁
  have hb₁ : P₁.par₂ none = none := rfl
  have hb₂ : (none : Option V) ≠ P₁.root := by simp [hP₁, insertAbove]
  have hL₂ := hL₁.addSite hb₁ hb₂ hi hU' (fun r => by
    have hiff : Anc P₁ none (some (leaf r)) ↔ r ∈ C := anc_insertAbove_none.trans (hnr r)
    by_cases hr : r ∈ C
    · rw [ite_eq_left (hiff.2 hr)]
      exact (hrows r).1 hr
    · rw [ite_eq_right fun h => hr (hiff.1 h)]
      have := fun h => hr ((hrows r).2 h)
      cases h₃ : A r i <;> cases h₄ : S i <;> simp_all)
  have h₀ : P₁.recombCount ≤ P.recombCount := recombCount_insertAbove_same
  refine ⟨Option V, inferInstance, SongHein2005.addSite P₁ none hb₁ hb₂ i (S i), timeOpt t τ, fun r => some (leaf r), ?_, hL₂, h₀.trans hc⟩
  exact ⟨R₁.t_par, R₁.t_par₂, R₁.t_root, R₁.t_leaf, R₁.J, R₁.K⟩

end Steps

section Initial

universe w

variable {ι : Type*} [LinearOrder ι] {X : Type w} [Fintype X] [DecidableEq X] {T : TimeOrderedTree X}

/-- The parent of a cluster in `T`. -/
def treeParent (T : TimeOrderedTree X) (D : Finset X) : Option (Option {D // D ∈ T.clusters}) :=
  if h : D = Finset.univ then some none else some (some ⟨(exists_parent (T := T) h).choose, (exists_parent (T := T) h).choose_spec.1⟩)

/-- **The first tree, with no site placed and no recombination** (`ext:song_hein_init`). Its nodes are its clusters and a root above them. -/
theorem hasState_init (S : ι → Bool) (A : X → ι → Bool) : HasState T S ⊥ A 0 := by
  have hparent : ∀ D : Finset X, ∀ h : D ≠ Finset.univ, (exists_parent (T := T) h).choose ∈ T.clusters ∧ D ⊂ (exists_parent (T := T) h).choose ∧
      ∀ E ∈ T.clusters, D ⊂ E → D.Nonempty → (exists_parent (T := T) h).choose ⊆ E := fun D h => (exists_parent (T := T) h).choose_spec
  set t : Option {D // D ∈ T.clusters} → EReal := fun v => match v with
    | none => ⊥
    | some D => tm T D.1 with ht
  set par : Option {D // D ∈ T.clusters} → Option (Option {D // D ∈ T.clusters}) := fun v => match v with
    | none => none
    | some D => treeParent T D.1 with hpar
  have hpar_lt : ∀ v a, par v = some a → t a < t v := by
    rintro (- | ⟨D, hD⟩) a ha
    · simp [hpar] at ha
    · simp only [hpar, treeParent] at ha
      split_ifs at ha with h
      · obtain rfl := Option.some_inj.1 ha
        exact bot_lt_iff_ne_bot.2 (tm_ne_bot D)
      · obtain rfl := Option.some_inj.1 ha
        obtain ⟨h₁, h₂, -⟩ := hparent D h
        exact tm_lt_of_ssubset hD h₁ h₂
  let P : PreNet ι (Option {D // D ∈ T.clusters}) :=
    { root := none
      par := par
      par₂ := fun _ => none
      site := fun _ => none
      label := fun _ => S
      par_eq_none := by
        rintro (- | ⟨D, hD⟩)
        · simp [hpar]
        · simp only [hpar, treeParent, reduceCtorEq, iff_false]
          split_ifs <;> simp
      par₂_root := rfl
      par₂_ne := by simp
      acyclic := acyclic_of_strict t (fun a b hab => by
        rcases hab with hab | hab
        · exact hpar_lt _ _ hab
        · simp at hab)
      site_tree := by simp
      label_tree := by simp
      label_recomb := by simp }
  set leaf : X → Option {D // D ∈ T.clusters} := fun r => some ⟨{r}, T.isHierarchy.2.1 r⟩ with hleaf
  -- The paths.
  have hup : ∀ {D : Finset X} (hD : D ∈ T.clusters) (z), Anc P z (some ⟨D, hD⟩) → match z with
      | none => True
      | some E => D ⊆ E.1 := by
    intro D hD z hz
    induction hz with
    | refl => exact subset_rfl
    | @tail z₁ z₂ _ hstep ih =>
      rcases z₁ with - | ⟨E, hE⟩
      · simp [P, hpar] at hstep
      · rcases z₂ with - | E₂
        · trivial
        · change treeParent T E = some (some E₂) at hstep
          unfold treeParent at hstep
          split_ifs at hstep with h
          · simp at hstep
          · have hE₂ := Option.some_inj.1 (Option.some_inj.1 hstep)
            obtain ⟨-, h₂, -⟩ := hparent E h
            subst hE₂
            exact (ih : D ⊆ E).trans h₂.subset
  have hdown : ∀ (n : ℕ) (D : Finset X) (hD : D ∈ T.clusters) (E : Finset X) (hE : E ∈ T.clusters), (E \ D).card = n → D ⊆ E → Anc P (some ⟨E, hE⟩) (some ⟨D, hD⟩) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro D hD E hE hn hDE
      rcases hDE.eq_or_ssubset with rfl | hss
      · exact Anc.refl _
      · have hne : D ≠ Finset.univ := fun h => by
          rw [h] at hss
          exact absurd hss.subset (fun h' => hss.2 (Finset.subset_univ _))
        obtain ⟨h₁, h₂, h₃⟩ := hparent D hne
        have hDne := T.isHierarchy.2.2.1 D hD
        have hPE := h₃ E hE hss hDne
        have hstep : P.par (some ⟨D, hD⟩) = some (some ⟨_, h₁⟩) := by
          change treeParent T D = _
          unfold treeParent
          rw [dite_eq_right hne]
        refine Anc.head hstep (ih _ ?_ _ h₁ E hE rfl hPE)
        rw [← hn]
        refine Finset.card_lt_card ⟨Finset.sdiff_subset_sdiff subset_rfl h₂.subset, fun h' => ?_⟩
        obtain ⟨x, hx, hxD⟩ := Finset.exists_of_ssubset h₂
        have := h' (Finset.mem_sdiff.2 ⟨hPE hx, hxD⟩)
        exact (Finset.mem_sdiff.1 this).2 hx
  have htop : ∀ (D : Finset X) (hD : D ∈ T.clusters), Anc P none (some ⟨D, hD⟩) := by
    intro D hD
    have h₁ := hdown _ D hD _ T.isHierarchy.1 rfl (Finset.subset_univ D)
    refine Anc.trans (Anc.of_par ?_) h₁
    change treeParent T Finset.univ = _
    unfold treeParent
    rw [dite_eq_left rfl]
  have hmemiff : ∀ (E : Finset X) (hE : E ∈ T.clusters) (r : X), Anc P (some ⟨E, hE⟩) (leaf r) ↔ r ∈ E := by
    intro E hE r
    constructor
    · intro h
      have := hup (T.isHierarchy.2.1 r) _ h
      exact (this : {r} ⊆ E) (Finset.mem_singleton_self r)
    · intro h
      exact hdown _ _ (T.isHierarchy.2.1 r) E hE rfl (Finset.singleton_subset_iff.2 h)
  refine ⟨Option {D // D ∈ T.clusters}, inferInstance, P, t, leaf, ⟨hpar_lt, by simp [P], rfl, ?_, ?_, ?_⟩, ⟨rfl, by simp [P], fun _ _ _ => rfl, by simp, by simp [P]⟩, by simp [PreNet.recombCount, P]⟩
  · intro r
    simp [ht, hleaf, tm]
  · rintro (- | ⟨E, hE⟩) r r' hn
    · change _ ↔ r' ∈ lin T r ⊥
      rw [lin_bot]
      exact ⟨fun _ => Finset.mem_univ _, fun _ => htop _ _⟩
    · have hr := (hmemiff E hE r).1 hn
      rw [hmemiff]
      change _ ↔ r' ∈ lin T r (tm T E)
      rw [lin_tm hE hr]
  · intro D hD
    obtain ⟨r, hr⟩ := T.isHierarchy.2.2.1 D hD
    exact ⟨some ⟨D, hD⟩, r, hr, (hmemiff D hD r).2 hr, rfl⟩

end Initial

/-- A finite distance is attained. -/
theorem exists_steps_of_ne_top {X : Type*} [Fintype X] [DecidableEq X] {T T' : TimeOrderedTree X} (h : T.doSPR T' ≠ ⊤) :
    ∃ k, TimeOrderedTree.SPRSteps k T T' ∧ (k : ℕ∞) = T.doSPR T' := by
  have hne : ((↑) '' {k | TimeOrderedTree.SPRSteps k T T'} : Set ℕ∞).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact h (by rw [TimeOrderedTree.doSPR, hemp, sInf_empty])
  obtain ⟨k, hk, hkeq⟩ := csInf_mem hne
  exact ⟨k, hk, hkeq⟩

/-- **The fact of Song and Hein 2005** (`ext:song_hein`) (Gusfield et al., line 654): "if `P = T_1, T_2, ..., T_m` is a sequence of time-ordered leaf-labeled trees in which `T_i` is compatible with site `i`
in `M`, for all `i`, then `R¹(M) ≤ L(P)`". The trees needn't be binary, while those of the source are, with their internal nodes totally ordered: this is stronger than the source. The source's ordered-SPR operation keeps the order of the other internal nodes, where `TimeOrderedTree.IsOrderedSPR` keeps their times, and times can be chosen along a path of the source so that its steps are steps here. A constant column isn't compatible with any tree here, while the source calls it compatible with every tree.

The source's equations (3), (5) say more, that the minimum of `L(P)` is `R¹(M)`, and it gives no proof of either inequality: only the construction in words, followed here. The other inequality is `SongHein2005.exists_sprLength_eq_R`, in `External.SongHein2005.Minimal`. See the `README.md`. -/
theorem R_le_sprLength {m : ℕ} (M : Finset (Fin m → Bool)) (hM : M.Nonempty) (P : Fin m → TimeOrderedTree M)
    (hP : ∀ i, (P i).CompatibleWith fun r => (r : Fin m → Bool) i) :
    (R .single M : ℕ∞) ≤ sprLength (List.ofFn P) := by
  have hempty : ∀ hm : m = 0, (R .single M : ℕ∞) ≤ sprLength (List.ofFn P) := by
    intro hm
    subst hm
    obtain ⟨r₀, hr₀⟩ := hM
    let Q : PreNet (Fin 0) Unit :=
      { root := ()
        par := fun _ => none
        par₂ := fun _ => none
        site := fun _ => none
        label := fun _ => r₀
        par_eq_none := by simp
        par₂_root := rfl
        par₂_ne := by simp
        acyclic := fun v h => by
          obtain ⟨_, -, h'⟩ := Relation.TransGen.tail'_iff.1 h
          simp at h'
        site_tree := by simp
        label_tree := by simp
        label_recomb := by simp }
    obtain ⟨a, b, N, h₁, h₂, -, h₄⟩ := Q.exists_network (c := .single) (M := M) (fun i => i.elim0) (by simp [Q]) ⟨r₀, hr₀⟩ (fun i => i.elim0)
      fun r _ => ⟨(), Subsingleton.elim _ _⟩
    have h₀ : Q.recombCount = 0 := by simp [PreNet.recombCount, Q]
    have hR : R .single M ≤ 0 := (R_le_recombCount N h₁ h₂).trans (h₄.trans h₀.le)
    rw [Nat.le_zero.1 hR]
    simp
  by_cases htop : sprLength (List.ofFn P) = ⊤
  · rw [htop]
    exact le_top
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact hempty hm
  have hdata : ∀ i, ∃ (C : Finset M) (a : Bool), C ∈ (P i).clusters ∧ C ≠ Finset.univ ∧ ∀ r : M, r ∈ C ↔ (r : Fin m → Bool) i = a := by
    intro i
    obtain ⟨C, hC, hne, h | h⟩ := hP i
    · exact ⟨C, true, hC, hne, fun r => by simp [h]⟩
    · exact ⟨C, false, hC, hne, fun r => by simp [h]⟩
  choose C a hC₁ hC₂ hC₃ using hdata
  set S : Fin m → Bool := fun i => !a i with hS
  set A : M → Fin m → Bool := fun r i => (r : Fin m → Bool) i with hA
  have hrows : ∀ i r, r ∈ C i ↔ A r i = !S i := fun i r => by
    rw [hC₃ i r]
    simp [hS, hA]
  have hconst : NoConstantColumn M := by
    intro i
    obtain ⟨r, hr⟩ := (P i).isHierarchy.2.2.1 _ (hC₁ i)
    obtain ⟨r', hr'⟩ : ∃ r', r' ∉ C i := by
      by_contra hno
      push Not at hno
      exact hC₂ i (Finset.eq_univ_of_forall hno)
    refine ⟨r.1, r.2, r'.1, r'.2, fun h => hr' ((hC₃ i r').2 ?_)⟩
    rw [← h]
    exact (hC₃ i r).1 hr
  set U : ℕ → LowerSet (Fin m) := fun n => ⟨{i | i.val < n}, fun a b hij (hi : a.val < n) => show b.val < n from lt_of_le_of_lt (show b.val ≤ a.val from hij) hi⟩ with hU
  have hUsucc : ∀ (n : ℕ) (hn : n < m) (j : Fin m), j ∈ U (n + 1) ↔ j ∈ U n ∨ j = ⟨n, hn⟩ := by
    intro n hn j
    change j.val < n + 1 ↔ j.val < n ∨ j = ⟨n, hn⟩
    rw [Fin.ext_iff]
    simp only
    omega
  have hUnot : ∀ (n : ℕ) (hn : n < m), (⟨n, hn⟩ : Fin m) ∉ U n := fun n hn h => lt_irrefl n h
  set L := List.ofFn P with hL
  have hlen : L.length = m := List.length_ofFn
  have hdrop : ∀ (j : ℕ) (h : j < m), L.drop j = P ⟨j, h⟩ :: L.drop (j + 1) := by
    intro j h
    have hget : L[j]'(by rw [hlen]; exact h) = P ⟨j, h⟩ := by simp [hL]
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact h), hget]
  have hmain : ∀ (n : ℕ) (hn : n < m), ∃ k : ℕ, (k : ℕ∞) + sprLength (L.drop n) ≤ sprLength L ∧ HasState (P ⟨n, hn⟩) S (U n) A k := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨0, by simp, ?_⟩
      have hU0 : U 0 = ⊥ := by
        ext i
        simp [hU]
      rw [hU0]
      exact hasState_init S A
    | succ n ih =>
      intro hn
      have hn' : n < m := by omega
      obtain ⟨k, hk, hst⟩ := ih hn'
      have hst' := hst.addSite (hC₁ ⟨n, hn'⟩) (hUnot n hn') (hUsucc n hn') (hrows ⟨n, hn'⟩)
      have hdn : L.drop n = P ⟨n, hn'⟩ :: P ⟨n + 1, hn⟩ :: L.drop (n + 2) := by
        rw [hdrop n hn', hdrop (n + 1) hn]
      have hdn' : sprLength (L.drop n) = (P ⟨n, hn'⟩).doSPR (P ⟨n + 1, hn⟩) + sprLength (L.drop (n + 1)) := by
        rw [hdn, hdrop (n + 1) hn]
        rfl
      rw [hdn'] at hk
      have hfin : (P ⟨n, hn'⟩).doSPR (P ⟨n + 1, hn⟩) ≠ ⊤ := by
        intro h
        rw [h] at hk
        simp only [top_add, add_top, top_le_iff] at hk
        exact htop hk
      obtain ⟨k₁, hk₁, hk₁eq⟩ := exists_steps_of_ne_top hfin
      refine ⟨k + k₁, ?_, hst'.steps hk₁⟩
      rw [Nat.cast_add, hk₁eq, add_assoc]
      exact hk
  obtain ⟨k, hk, hst⟩ := hmain (m - 1) (by omega)
  have hlast : (⟨m - 1, by omega⟩ : Fin m) ∉ U (m - 1) := hUnot (m - 1) (by omega)
  have hst' := hst.addSite (hC₁ _) hlast (hUsucc (m - 1) (by omega)) (hrows _)
  obtain ⟨V, _, Q, t, leaf, -, hLab, hcount⟩ := hst'
  have hall : ∀ i, i ∈ U (m - 1 + 1) := fun i => by
    change i.val < m - 1 + 1
    have := i.2
    omega
  obtain ⟨a', b', N, h₁, h₂, -, h₄⟩ := Q.exists_network (c := .single) (M := M) (fun i => (hLab.site i).2 (hall i))
    (fun x p q hp hq => by
      obtain ⟨L', -, hL'⟩ := hLab.obey x p q hp hq
      exact ⟨L', hL'⟩) hM hconst
    (fun r hr => ⟨leaf ⟨r, hr⟩, funext fun i => hLab.rows i (hall i) ⟨r, hr⟩⟩)
  have hR : R .single M ≤ k := (R_le_recombCount N h₁ h₂).trans (h₄.trans hcount)
  calc (R .single M : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hR
    _ ≤ (k : ℕ∞) + sprLength (L.drop (m - 1)) := le_self_add
    _ ≤ sprLength L := hk

end SongHein2005
